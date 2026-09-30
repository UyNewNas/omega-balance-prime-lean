import OmegaBalance.F3RootDepthHaar

/-!
# Null root points for actual Haar sampling

Singletons lie in every genuine residue fiber. The proved fiber masses,
compared with mathlib's arbitrarily small inverse powers of two, force
their actual Haar mass to vanish. Restriction and normalization preserve
this fact. No non-atomicity or root-nullity assumption is added.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Every singleton has zero mass under the concrete ambient Haar measure. -/
theorem f3PadicHaar_singleton (a : ℤ_[3]) : f3PadicHaar {a} = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hne
  have hsub : ({a} : Set ℤ_[3]) ⊆
      (PadicInt.toZModPow n) ⁻¹' {PadicInt.toZModPow n a} := by
    intro d hd
    have hd' : d = a := hd
    subst d
    simp
  have hmass : f3PadicHaar {a} ≤ ((3 : ℝ≥0∞) ^ n)⁻¹ := by
    simpa using (measure_mono hsub).trans_eq (padicInt_haar_fiber f3PadicHaar n _)
  have hcomp : ((3 : ℝ≥0∞) ^ n)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    rw [← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.mpr (pow_le_pow_left' (by norm_num) n)
  exact (not_lt_of_ge (hmass.trans hcomp)) hn

/-- Actual normalized unit Haar measure also gives every singleton mass zero. -/
theorem f3UnitHaar_singleton (a : ℤ_[3]) : f3UnitHaar {a} = 0 := by
  rw [f3UnitHaar, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton a), smul_eq_mul]
  have hzero : f3PadicHaar (({a} : Set ℤ_[3]) ∩ f3PadicUnitSet) = 0 :=
    le_antisymm ((measure_mono Set.inter_subset_left).trans_eq (f3PadicHaar_singleton a))
      zero_le
  rw [hzero, mul_zero]

/-- The infinite-depth event is exactly the null root point, not a zero-depth layer. -/
theorem f3UnitHaar_rootDepth_top (a : ℤ_[3]) :
    f3UnitHaar {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = ⊤} = 0 := by
  have hevent : {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = ⊤} = {a} := by
    ext d
    change rootDepth (d : ℚ_[3]) (a : ℚ_[3]) = ⊤ ↔ d = a
    rw [rootDepth_eq_top_iff]
    exact ⟨PadicInt.ext, fun h => congrArg (fun x : ℤ_[3] => (x : ℚ_[3])) h⟩
  rw [hevent, f3UnitHaar_singleton]

end

end OmegaBalance
