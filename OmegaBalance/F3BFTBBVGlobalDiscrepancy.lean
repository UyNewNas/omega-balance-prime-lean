import OmegaBalance.F3BFTBReciprocalTotient

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

end OmegaBalance
