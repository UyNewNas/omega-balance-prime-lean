import OmegaBalance.F3RootDepthLaw

/-!
# The original shared-root configuration under actual unit Haar sampling

These wrappers retain the existing `F3SharedRootConfig` model, including
positive base depth, at least two distinct unit roots, and a common residue
class. Its actual three-adic roots are converted to `ℤ_[3]` through mathlib's
`PadicInt.mkUnits`, with an exact coercion proof. The observations here are
the excess depths R; no integer prime-product identification is claimed.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The model's additive-valuation unit condition implies norm one. -/
theorem f3SharedRootConfig_root_norm {m : ℕ} (C : F3SharedRootConfig m) (i : Fin m) :
    ‖C.root i‖ = 1 := by
  have hne : C.root i ≠ 0 := by
    intro hz
    have h := C.root_unit i
    simp [hz] at h
  have hv := C.root_unit i
  rw [Padic.addValuation.apply hne] at hv
  have hv0 : (C.root i).valuation = 0 := by exact_mod_cast hv
  rw [Padic.norm_eq_zpow_neg_valuation hne, hv0]
  norm_num

/-- The same actual model root, now represented as a three-adic integer unit. -/
def f3SharedRootUnit {m : ℕ} (C : F3SharedRootConfig m) (i : Fin m) : ℤ_[3] :=
  ↑(PadicInt.mkUnits (f3SharedRootConfig_root_norm C i))

/-- Conversion does not move or replace the actual three-adic root. -/
theorem f3SharedRootUnit_coe {m : ℕ} (C : F3SharedRootConfig m) (i : Fin m) :
    (f3SharedRootUnit C i : ℚ_[3]) = C.root i :=
  PadicInt.mkUnits_eq (f3SharedRootConfig_root_norm C i)

/-- Each converted root is genuinely a unit of the three-adic integer ring. -/
theorem f3SharedRootUnit_isUnit {m : ℕ} (C : F3SharedRootConfig m) (i : Fin m) :
    IsUnit (f3SharedRootUnit C i) :=
  (PadicInt.mkUnits (f3SharedRootConfig_root_norm C i)).isUnit

/-- The single-root tail on the unchanged original shared-root configuration. -/
theorem f3SharedRootConfig_unitHaar_depth_ge {m : ℕ} (C : F3SharedRootConfig m)
    (i : Fin m) {t : ℕ} (ht : 1 ≤ t) :
    f3UnitHaar {d : ℤ_[3] | (t : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (C.root i)} =
      (2 * (3 : ℝ≥0∞) ^ (t - 1))⁻¹ := by
  simpa only [f3RootDepthTail, f3SharedRootUnit_coe] using
    (f3UnitHaar_rootDepth_ge (f3SharedRootUnit_isUnit C i) ht)

/-- The positive exact-layer law on the unchanged original configuration. -/
theorem f3SharedRootConfig_unitHaar_depth_eq {m : ℕ} (C : F3SharedRootConfig m)
    (i : Fin m) {t : ℕ} (ht : 1 ≤ t) :
    f3UnitHaar {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (C.root i) = (t : WithTop ℤ)} =
      ((3 : ℝ≥0∞) ^ t)⁻¹ := by
  simpa only [f3RootDepthLayer, f3SharedRootUnit_coe] using
    (f3UnitHaar_rootDepth_eq (f3SharedRootUnit_isUnit C i) ht)

/-- REC's single-observation certificate probability on its actual model.
The event compares excess depths; no infinite-depth subtraction is used. -/
theorem f3SharedRootConfig_unitHaar_depth_ne {m : ℕ} (C : F3SharedRootConfig m)
    {i j : Fin m} (_hij : i ≠ j) {L : ℕ}
    (hL : rootDistance (C.root i) (C.root j) = (L : WithTop ℤ)) :
    f3UnitHaar {d : ℤ_[3] | rootDepth (d : ℚ_[3]) (C.root i) ≠
      rootDepth (d : ℚ_[3]) (C.root j)} = ((3 : ℝ≥0∞) ^ L)⁻¹ := by
  have hLpos : 1 ≤ L := by
    have h := C.roots_same_residue i j
    rw [hL] at h
    exact_mod_cast h
  have hdist : rootDistance (f3SharedRootUnit C i : ℚ_[3])
      (f3SharedRootUnit C j : ℚ_[3]) = (L : WithTop ℤ) := by
    simpa only [f3SharedRootUnit_coe] using hL
  simpa only [f3SharedRootUnit_coe] using
    (f3UnitHaar_rootDepth_ne (f3SharedRootUnit_isUnit C i)
      (f3SharedRootUnit_isUnit C j) hLpos hdist)

end

end OmegaBalance
