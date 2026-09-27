import OmegaBalance.F3BFTBReciprocalTotient
import Mathlib.Tactic

namespace OmegaBalance

open Classical Finset
open scoped BigOperators

/--
A global main-term discrepancy paid once at every positive modulus costs only
a logarithmic square after the reciprocal-totient ledger.
-/
theorem bftb_sum_abs_discrepancy_div_totient_le
    (R : ℕ) (d : ℝ) :
    (∑ q ∈ Finset.Icc 1 R, |d| / (q.totient : ℝ)) ≤
      |d| * (1 + Real.log R) ^ 2 := by
  calc
    (∑ q ∈ Finset.Icc 1 R, |d| / (q.totient : ℝ))
        = |d| * ∑ q ∈ Finset.Icc 1 R, ((q.totient : ℝ)⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [div_eq_mul_inv]
    _ ≤ |d| * (1 + Real.log R) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (bftb_sum_inv_totient_le_one_add_log_sq R) (abs_nonneg d)

/--
The already-proved unit-residue Li-to-pi normalization, specialized to the
full positive modulus interval, with its complete reciprocal-totient loss
compressed to a log-square factor.
-/
theorem bftb_sum_iSup_abs_main_term_change_Icc
    (R : ℕ) (x : ∀ q : ℕ, (ZMod q)ˣ → ℝ) (li pi : ℝ) :
    (∑ q ∈ Finset.Icc 1 R, ⨆ a : (ZMod q)ˣ,
        |x q a - pi / (q.totient : ℝ)|) ≤
      (∑ q ∈ Finset.Icc 1 R, ⨆ a : (ZMod q)ˣ,
        |x q a - li / (q.totient : ℝ)|) +
        |li - pi| * (1 + Real.log R) ^ 2 := by
  refine (bftb_sum_iSup_abs_main_term_change_totient
    (Finset.Icc 1 R) (fun q hq => (Finset.mem_Icc.mp hq).1)
    x li pi).trans ?_
  exact add_le_add (le_refl _)
    (bftb_sum_abs_discrepancy_div_totient_le R (li - pi))

/--
Abstract q=1 extraction used by the StandardBV adapter. If a nonnegative
prefix error dominates the local q=1 endpoint error, then its modulus sum
dominates the global prime-counting/main-term discrepancy.
-/
theorem bftb_global_discrepancy_le_modulus_sum
    (main : ℕ → ℝ) (x R : ℕ) (hR : 1 ≤ R)
    (pref : ℕ → ℝ)
    (hnonneg : ∀ q ∈ Finset.Icc 1 R, 0 ≤ pref q)
    (hone : bftbCanonicalPrimeAPMaxError main x 1 ≤ pref 1) :
    |(Nat.primeCounting x : ℝ) - main x| ≤
      ∑ q ∈ Finset.Icc 1 R, pref q := by
  rw [← bftbCanonicalPrimeAPMaxError_one main x]
  exact hone.trans
    (Finset.single_le_sum
      (fun q hq => hnonneg q hq)
      (by simp [hR]))


/-- The normalization factor `1 + (1 + L)^2` costs at most five squares once `L ≥ 1`. -/
theorem bftb_one_add_sq_le_five_sq
    (L : ℝ) (hL : 1 ≤ L) :
    1 + (1 + L) ^ 2 ≤ 5 * L ^ 2 := by
  have hprod : 0 ≤ (2 * L + 1) * (L - 1) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hL)
  nlinarith

/-- Monotonicity of the reciprocal-totient logarithmic-square loss in its cutoff. -/
theorem bftb_one_add_log_sq_mono
    {R N : ℕ} (hR : 1 ≤ R) (hRN : R ≤ N) :
    (1 + Real.log R) ^ 2 ≤ (1 + Real.log N) ^ 2 := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hR)
  have hlog : Real.log (R : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log hRpos (by exact_mod_cast hRN)
  have hleft : 0 ≤ 1 + Real.log (R : ℝ) := by
    have h := Real.log_natCast_nonneg R
    linarith
  have hright : 0 ≤ 1 + Real.log (N : ℝ) := by
    have h := Real.log_natCast_nonneg N
    linarith
  exact (sq_le_sq₀ hleft hright).2 (by linarith)

/-- Two extra logarithmic powers absorb the complete Li-to-pi normalization loss. -/
theorem bftb_one_add_log_sq_factor_le
    {R N : ℕ} (hR : 1 ≤ R) (hRN : R ≤ N)
    (hlogN : 1 ≤ Real.log (N : ℝ)) :
    1 + (1 + Real.log R) ^ 2 ≤
      5 * Real.log N ^ 2 := by
  calc
    1 + (1 + Real.log R) ^ 2
        ≤ 1 + (1 + Real.log N) ^ 2 := by
          exact add_le_add_left (bftb_one_add_log_sq_mono hR hRN) 1
    _ ≤ 5 * Real.log N ^ 2 :=
      bftb_one_add_sq_le_five_sq (Real.log (N : ℝ)) hlogN

/-- The same logarithmic-loss absorption is eventually available at natural endpoints. -/
theorem bftb_eventually_one_add_log_sq_le_five_log_sq :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 + (1 + Real.log (N : ℝ)) ^ 2 ≤
        5 * Real.log (N : ℝ) ^ 2 := by
  have hlog :
      Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
  exact bftb_one_add_sq_le_five_sq (Real.log (N : ℝ)) hN

end OmegaBalance
