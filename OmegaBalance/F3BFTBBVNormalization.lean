import OmegaBalance.F3BFTBManyPrimesAdapter
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace OmegaBalance

/--
Changing an arithmetic-progression main term from `li / d` to `pi / d`
costs at most the global main-term discrepancy divided by the same positive
denominator.
-/
theorem bftb_abs_main_term_change_div
    (x li pi d : ℝ) (hd : 0 < d) :
    |x - pi / d| ≤ |x - li / d| + |li - pi| / d := by
  have hdecomp :
      x - pi / d = (x - li / d) + (li - pi) / d := by
    ring
  rw [hdecomp]
  calc
    |(x - li / d) + (li - pi) / d|
        ≤ |x - li / d| + |(li - pi) / d| := abs_add _ _
    _ = |x - li / d| + |li - pi| / d := by
      rw [abs_div, abs_of_pos hd]

/-- Specialize the Li-to-pi normalization inequality to Euler's totient. -/
theorem bftb_abs_main_term_change_totient
    {q : ℕ} (hq : 0 < q) (x li pi : ℝ) :
    |x - pi / (q.totient : ℝ)| ≤
      |x - li / (q.totient : ℝ)| + |li - pi| / (q.totient : ℝ) := by
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast hφnat
  exact bftb_abs_main_term_change_div x li pi (q.totient : ℝ) hφ

/--
For a positive modulus, the denominator `φ(q)` is at least one, so the
normalization cost is at most the global discrepancy `|li - pi|`.
-/
theorem bftb_abs_main_term_change_totient_le
    {q : ℕ} (hq : 0 < q) (x li pi : ℝ) :
    |x - pi / (q.totient : ℝ)| ≤
      |x - li / (q.totient : ℝ)| + |li - pi| := by
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφoneNat : 1 ≤ q.totient := Nat.succ_le_iff.mpr hφnat
  have hφone : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast hφoneNat
  calc
    |x - pi / (q.totient : ℝ)|
        ≤ |x - li / (q.totient : ℝ)| +
            |li - pi| / (q.totient : ℝ) :=
      bftb_abs_main_term_change_totient hq x li pi
    _ ≤ |x - li / (q.totient : ℝ)| + |li - pi| := by
      exact add_le_add_left (div_le_self (abs_nonneg _) hφone) _

end OmegaBalance
