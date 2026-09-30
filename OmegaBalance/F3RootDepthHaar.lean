import OmegaBalance.F3UnitHaar
import OmegaBalance.F3RootCertificates
import Lean.Elab.Tactic.Omega

/-!
# Actual three-adic depth tails under normalized unit Haar measure

The root depth is the existing `WithTop ℤ` valuation on actual `ℚ_[3]`.
The residue bridge splits out a sample at the root before using mathlib's
finite valuation. In particular no totalized value `valuation 0 = 0` is used
as the observable. This is the local probability input to REC-L3.
-/

namespace OmegaBalance

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Actual extended root depth is at least `t` exactly on a residue fiber. -/
theorem rootDepth_ge_iff_toZModPow (d a : ℤ_[3]) (t : ℕ) :
    (t : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3]) ↔
      PadicInt.toZModPow t d = PadicInt.toZModPow t a := by
  by_cases h : d = a
  · subst d
    rw [(rootDepth_eq_top_iff _ _).mpr rfl]
    simp
  have hcoe : (d : ℚ_[3]) ≠ (a : ℚ_[3]) := fun e => h (PadicInt.ext e)
  rw [rootDepth_eq_valuation hcoe, ← PadicInt.coe_sub, PadicInt.valuation_coe]
  change ((t : ℤ) : WithTop ℤ) ≤ (((d - a).valuation : ℤ) : WithTop ℤ) ↔ _
  rw [WithTop.coe_le_coe, Nat.cast_le,
    ← PadicInt.mem_span_pow_iff_le_valuation (d - a) (sub_ne_zero.mpr h),
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- A finite threshold event for the actual extended depth. -/
def f3RootDepthTail (a : ℤ_[3]) (t : ℕ) : Set ℤ_[3] :=
  {d | (t : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3])}

/-- Root-depth tails are genuine residue fibers, including the infinite root point. -/
theorem f3RootDepthTail_eq_fiber (a : ℤ_[3]) (t : ℕ) :
    f3RootDepthTail a t = (PadicInt.toZModPow t) ⁻¹' {PadicInt.toZModPow t a} := by
  ext d
  exact rootDepth_ge_iff_toZModPow d a t

/-- The actual depth threshold events are measurable. -/
theorem f3RootDepthTail_measurable (a : ℤ_[3]) (t : ℕ) :
    MeasurableSet (f3RootDepthTail a t) := by
  rw [f3RootDepthTail_eq_fiber]
  exact padicInt_measurable_fiber t _

/-- The zero threshold is automatic on three-adic integers. -/
theorem f3RootDepthTail_zero (a : ℤ_[3]) : f3RootDepthTail a 0 = Set.univ := by
  rw [f3RootDepthTail_eq_fiber]
  ext d
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact Subsingleton.elim _ _

/-- Depth tails decrease as the threshold increases. -/
theorem f3RootDepthTail_antitone (a : ℤ_[3]) : Antitone (f3RootDepthTail a) := by
  intro s t hst d hd
  change (s : WithTop ℤ) ≤ rootDepth (d : ℚ_[3]) (a : ℚ_[3])
  have hst' : (s : WithTop ℤ) ≤ (t : WithTop ℤ) := by exact_mod_cast hst
  exact hst'.trans hd

/-- The single-root probability is the normalized actual Haar fiber mass. -/
theorem f3UnitHaar_rootDepth_ge {a : ℤ_[3]} (ha : IsUnit a) {t : ℕ} (ht : 1 ≤ t) :
    f3UnitHaar (f3RootDepthTail a t) = (2 * (3 : ℝ≥0∞) ^ (t - 1))⁻¹ := by
  rw [f3RootDepthTail_eq_fiber, f3UnitHaar_fiber ha ht]
  cases t with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one, pow_succ]
    rw [ENNReal.inv_div (by norm_num) (by norm_num),
      ENNReal.mul_inv (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ ⊤))
        (Or.inr (by norm_num : (3 : ℝ≥0∞) ≠ 0)),
      ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)), div_eq_mul_inv]
    calc
      (3 : ℝ≥0∞) * 2⁻¹ * ((3 ^ n)⁻¹ * 3⁻¹) =
          (3 * 3⁻¹) * (2⁻¹ * (3 ^ n)⁻¹) := by ac_rfl
      _ = 2⁻¹ * (3 ^ n)⁻¹ := by
        rw [ENNReal.mul_inv_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0)
          (by norm_num : (3 : ℝ≥0∞) ≠ ⊤), one_mul]

end

end OmegaBalance
