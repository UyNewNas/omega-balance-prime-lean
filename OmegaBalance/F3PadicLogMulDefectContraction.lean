import OmegaBalance.F3PadicLogMulDefectBound

/-!
# Depth-sensitive contraction of the p-adic logarithm multiplication defect

The uniform 1/9 defect bound is sharpened here to a relative bound: the
defect is at least one ternary layer smaller than the larger input
principal-unit displacement. This remains a quantitative approximation; it
does not assert exact multiplicativity.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The nonlinear logarithm tail gains one full 3-adic layer relative to its
linear displacement. -/
theorem norm_f3PadicLogTail_le_delta_div_three {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicLogTail n‖ ≤ ‖f3PadicDelta n‖ / 3 := by
  have hx : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  calc
    ‖f3PadicLogTail n‖
        ≤ (3 : ℝ) ^ (-((f3PadicDelta n).valuation + 1) : ℤ) :=
      norm_f3PadicLogTail_le_next_radius hn h3
    _ = ‖f3PadicDelta n‖ / 3 := by
      rw [Padic.norm_eq_zpow_neg_valuation hx]
      rw [show (-((f3PadicDelta n).valuation + 1) : ℤ) =
          (-(f3PadicDelta n).valuation : ℤ) + (-1 : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg_one, div_eq_mul_inv]

/-- The product displacement never has larger norm than the larger input
displacement on the admissible principal-unit ball. -/
theorem norm_f3PadicDelta_product_le_max {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta (m * n)‖ ≤
      max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ := by
  rw [f3PadicDelta_mul hm3 hn3]
  apply le_trans (IsUltrametricDist.norm_add_le_max _ _)
  apply max_le
  · exact IsUltrametricDist.norm_add_le_max _ _
  · rw [norm_mul]
    have hn_le_one : ‖f3PadicDelta n‖ ≤ (1 : ℝ) := by
      exact le_trans (f3PadicDelta_norm_le_one_third hn hn3) (by norm_num)
    calc
      ‖f3PadicDelta m‖ * ‖f3PadicDelta n‖
          ≤ ‖f3PadicDelta m‖ * 1 :=
        mul_le_mul_of_nonneg_left hn_le_one (norm_nonneg _)
      _ = ‖f3PadicDelta m‖ := by ring
      _ ≤ max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ := le_max_left _ _

/-- The quadratic displacement term gains one full layer relative to the
larger of the two input displacements. -/
theorem norm_f3PadicDelta_mul_le_max_div_three {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta m * f3PadicDelta n‖ ≤
      max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ / 3 := by
  rw [norm_mul]
  have hn_le := f3PadicDelta_norm_le_one_third hn hn3
  calc
    ‖f3PadicDelta m‖ * ‖f3PadicDelta n‖
        ≤ ‖f3PadicDelta m‖ * (3 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hn_le (norm_nonneg _)
    _ ≤ max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ * (3 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ / 3 := by
      rw [div_eq_mul_inv]

/-- The genuine logarithmic multiplication defect is contracted by one full
3-adic layer relative to the larger input displacement. -/
theorem f3PadicLog_mul_defect_norm_le_max_div_three {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicLog (m * n) - (f3PadicLog m + f3PadicLog n)‖ ≤
      max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖ / 3 := by
  have hn1 : 1 ≤ n := by omega
  have hmn : 1 < m * n := lt_of_lt_of_le hm (by
    simpa using Nat.mul_le_mul_left m hn1)
  have h3mn : ¬ 3 ∣ m * n := f3_three_not_dvd_mul hm3 hn3
  let M : ℝ := max ‖f3PadicDelta m‖ ‖f3PadicDelta n‖
  have hquad :
      ‖f3PadicDelta m * f3PadicDelta n‖ ≤ M / 3 := by
    simpa [M] using norm_f3PadicDelta_mul_le_max_div_three hm hn hm3 hn3
  have hprod_delta :
      ‖f3PadicDelta (m * n)‖ ≤ M := by
    simpa [M] using norm_f3PadicDelta_product_le_max hm hn hm3 hn3
  have hprod_tail :
      ‖f3PadicLogTail (m * n)‖ ≤ M / 3 := by
    exact le_trans
      (norm_f3PadicLogTail_le_delta_div_three hmn h3mn)
      (div_le_div_of_nonneg_right hprod_delta (by norm_num))
  have hm_tail :
      ‖f3PadicLogTail m‖ ≤ M / 3 := by
    exact le_trans
      (norm_f3PadicLogTail_le_delta_div_three hm hm3)
      (div_le_div_of_nonneg_right (by
        simpa [M] using (le_max_left ‖f3PadicDelta m‖ ‖f3PadicDelta n‖))
        (by norm_num))
  have hn_tail :
      ‖f3PadicLogTail n‖ ≤ M / 3 := by
    exact le_trans
      (norm_f3PadicLogTail_le_delta_div_three hn hn3)
      (div_le_div_of_nonneg_right (by
        simpa [M] using (le_max_right ‖f3PadicDelta m‖ ‖f3PadicDelta n‖))
        (by norm_num))
  rw [f3PadicLog_mul_defect_eq hm hn hm3 hn3]
  simp only [sub_eq_add_neg]
  have hfirst :
      ‖f3PadicDelta m * f3PadicDelta n + f3PadicLogTail (m * n)‖ ≤
        M / 3 := by
    exact le_trans
      (IsUltrametricDist.norm_add_le_max _ _)
      (max_le hquad hprod_tail)
  have hsecond :
      ‖(f3PadicDelta m * f3PadicDelta n + f3PadicLogTail (m * n)) +
          -f3PadicLogTail m‖ ≤ M / 3 := by
    exact le_trans
      (IsUltrametricDist.norm_add_le_max _ _)
      (max_le hfirst (by simpa using hm_tail))
  have hfinal :
      ‖((f3PadicDelta m * f3PadicDelta n + f3PadicLogTail (m * n)) +
          -f3PadicLogTail m) + -f3PadicLogTail n‖ ≤ M / 3 := by
    exact le_trans
      (IsUltrametricDist.norm_add_le_max _ _)
      (max_le hsecond (by simpa using hn_tail))
  simpa [M] using hfinal

end OmegaBalance
