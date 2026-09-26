import OmegaBalance.F3PadicLogMulDefect

/-!
# First quantitative bound on the p-adic logarithm multiplication defect

This module proves that the defect isolated in `F3PadicLogMulDefect` is
uniformly second-order on the F₃ principal-unit domain.  It still does not
assert that the defect is zero.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Every nonlinear logarithm tail of an admissible F₃ input is at most the
next uniform radius `1/9`. -/
theorem norm_f3PadicLogTail_le_one_ninth {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicLogTail n‖ ≤ (9 : ℝ)⁻¹ := by
  have hf : f3 n ≠ 0 := f3_ne_zero_of_not_dvd hn h3
  have hv : (1 : ℤ) ≤ (f3PadicDelta n).valuation := by
    rw [f3PadicDelta_valuation hn h3]
    exact_mod_cast Int.natAbs_pos.mpr hf
  calc
    ‖f3PadicLogTail n‖
        ≤ (3 : ℝ) ^ (-((f3PadicDelta n).valuation + 1) : ℤ) :=
      norm_f3PadicLogTail_le_next_radius hn h3
    _ ≤ (3 : ℝ) ^ (-2 : ℤ) := by
      exact
        (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num)).monotone
          (by omega)
    _ = (9 : ℝ)⁻¹ := by norm_num [zpow_neg]

/-- The quadratic displacement term in the log-multiplication defect is also
uniformly at most `1/9`. -/
theorem norm_f3PadicDelta_mul_le_one_ninth {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta m * f3PadicDelta n‖ ≤ (9 : ℝ)⁻¹ := by
  rw [norm_mul]
  have hm_le := f3PadicDelta_norm_le_one_third hm hm3
  have hn_le := f3PadicDelta_norm_le_one_third hn hn3
  calc
    ‖f3PadicDelta m‖ * ‖f3PadicDelta n‖
        ≤ (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ :=
      mul_le_mul hm_le hn_le (norm_nonneg _) (by positivity)
    _ = (9 : ℝ)⁻¹ := by norm_num

/-- The genuine logarithm is multiplicative modulo the next 3-adic layer:
the whole defect has norm at most `1/9`.  This is a quantitative
second-order statement, not yet the final equality. -/
theorem f3PadicLog_mul_defect_norm_le_one_ninth {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicLog (m * n) - (f3PadicLog m + f3PadicLog n)‖ ≤
      (9 : ℝ)⁻¹ := by
  have hn1 : 1 ≤ n := by omega
  have hmn : 1 < m * n := lt_of_lt_of_le hm (by
    simpa using Nat.mul_le_mul_left m hn1)
  have h3mn : ¬ 3 ∣ m * n := f3_three_not_dvd_mul hm3 hn3
  have hquad := norm_f3PadicDelta_mul_le_one_ninth hm hn hm3 hn3
  have hprod := norm_f3PadicLogTail_le_one_ninth hmn h3mn
  have hm_tail := norm_f3PadicLogTail_le_one_ninth hm hm3
  have hn_tail := norm_f3PadicLogTail_le_one_ninth hn hn3
  rw [f3PadicLog_mul_defect_eq hm hn hm3 hn3]
  simp only [sub_eq_add_neg]
  have hfirst :
      ‖f3PadicDelta m * f3PadicDelta n + f3PadicLogTail (m * n)‖ ≤
        (9 : ℝ)⁻¹ := by
    exact le_trans
      (IsUltrametricDist.norm_add_le_max _ _)
      (max_le hquad hprod)
  have hsecond :
      ‖(f3PadicDelta m * f3PadicDelta n + f3PadicLogTail (m * n)) +
          -f3PadicLogTail m‖ ≤ (9 : ℝ)⁻¹ := by
    exact le_trans
      (IsUltrametricDist.norm_add_le_max _ _)
      (max_le hfirst (by simpa using hm_tail))
  exact le_trans
    (IsUltrametricDist.norm_add_le_max _ _)
    (max_le hsecond (by simpa using hn_tail))

end OmegaBalance
