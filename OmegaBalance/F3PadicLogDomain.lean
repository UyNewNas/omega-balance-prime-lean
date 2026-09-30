import OmegaBalance.F3Coordinates
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The principal-unit p-adic domain behind the F₃ logarithmic coordinate

This module does not define the p-adic logarithm yet.  It embeds the existing
integer coordinate `f3Unit` into `ℚ_[3]` and proves the exact valuation and
norm facts needed to place it in the open principal-unit ball where the
logarithm series must be constructed.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The sign character requested for the logarithmic coordinate.  On the
ordinary domain `3 ∤ n`, it is `+1` on `n ≡ 1 (mod 3)` and `-1` on
`n ≡ 2 (mod 3)`. -/
def f3Chi (n : ℕ) : ℤ := -f3Side n

/-- The existing integer unit is exactly `χ(n) n`. -/
theorem f3Unit_eq_chi_mul (n : ℕ) :
    f3Unit n = f3Chi n * (n : ℤ) := by
  simp [f3Unit, f3Chi]

/-- The signed F₃ value is `-χ(n)` times its unsigned 3-adic depth. -/
theorem f3_eq_neg_chi_mul_natAbs {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n = -f3Chi n * ((f3 n).natAbs : ℤ) := by
  unfold f3Chi
  simpa only [neg_neg] using f3_eq_side_mul_natAbs hn h3

/-- The existing normalized integer unit coordinate, embedded in the 3-adic field. -/
noncomputable def f3PadicUnit (n : ℕ) : ℚ_[3] :=
  (f3Unit n : ℚ_[3])

/-- The displacement from one of the 3-adic unit coordinate. -/
noncomputable def f3PadicDelta (n : ℕ) : ℚ_[3] :=
  f3PadicUnit n - 1

/-- Multiplicativity survives the embedding into the 3-adic field. -/
theorem f3PadicUnit_mul {m n : ℕ} (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3PadicUnit (m * n) = f3PadicUnit m * f3PadicUnit n := by
  simp only [f3PadicUnit, f3Unit_mul hm3 hn3, Int.cast_mul]

/-- The displacement is literally the cast of the existing integer displacement. -/
theorem f3PadicDelta_eq_intCast (n : ℕ) :
    f3PadicDelta n = ((f3Unit n - 1 : ℤ) : ℚ_[3]) := by
  simp [f3PadicDelta, f3PadicUnit]

/-- Exact valuation transfer from the integer coordinate into `ℚ_[3]`. -/
theorem f3PadicDelta_valuation {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    (f3PadicDelta n).valuation = (f3 n).natAbs := by
  rw [f3PadicDelta_eq_intCast, Padic.valuation_intCast]
  exact_mod_cast f3Unit_depth hn h3

/-- On the nontrivial domain the displacement from one is nonzero. -/
theorem f3PadicDelta_ne_zero {n : ℕ} (hn : 1 < n) :
    f3PadicDelta n ≠ 0 := by
  rw [f3PadicDelta_eq_intCast]
  exact_mod_cast f3Unit_sub_one_ne_zero hn

/-- Exact 3-adic norm of the displacement from one.  This is the isometry
statement for the pre-logarithmic coordinate. -/
theorem f3PadicDelta_norm {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta n‖ = (3 : ℝ) ^ (-(f3 n).natAbs : ℤ) := by
  rw [Padic.norm_eq_zpow_neg_valuation (f3PadicDelta_ne_zero hn),
    f3PadicDelta_valuation hn h3]
  norm_num

/-- Every admissible `F₃` input lands in the open principal-unit ball
`‖U(n)-1‖ < 1`, the actual convergence domain required by the 3-adic
logarithm series. -/
theorem f3PadicDelta_norm_lt_one {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta n‖ < 1 := by
  have hf : f3 n ≠ 0 := f3_ne_zero_of_not_dvd hn h3
  have habs : 0 < (f3 n).natAbs := Int.natAbs_pos.mpr hf
  rw [f3PadicDelta_norm hn h3]
  have hthree : (1 : ℝ) < 3 := by norm_num
  rw [zpow_lt_one_iff_right₀ hthree]
  exact Int.neg_neg_of_pos (by exact_mod_cast habs)

/-- The displacement is topologically nilpotent, i.e. its powers tend to zero.
This is the convergence-domain input for the actual logarithm series. -/
theorem f3PadicDelta_pow_tendsto_zero {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    Filter.Tendsto (fun k : ℕ => f3PadicDelta n ^ k) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (f3PadicDelta_norm_lt_one hn h3)

end OmegaBalance
