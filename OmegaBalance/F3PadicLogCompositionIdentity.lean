import OmegaBalance.F3PadicLogCompositionOutputCoeff

/-!
# Analytic multiplicativity of the genuine 3-adic F₃ logarithm

The formal logarithm identity and the two justified regroupings of the
absolutely summable triangular composition family now meet in one theorem:
the direct analytic logarithm of the principal-unit product increment equals
the sum of the two analytic logarithms.  Specializing to F₃ principal units
closes the multiplicativity part of LOG-1.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : AddCommGroup ℚ_[3] := instAddCommGroupPadic 3

/-- The genuine convergent 3-adic logarithm satisfies the principal-unit
multiplication law on the closed radius-`1/3` ball. -/
theorem f3PadicLogOnePlus_product
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (hxy : ‖x + y + x * y‖ < 1) :
    f3PadicLogOnePlus (x + y + x * y) =
      f3PadicLogOnePlus x + f3PadicLogOnePlus y := by
  let b : PowerSeries ℚ_[3] :=
    ((f3PadicLogMulPolynomial x y : Polynomial ℚ_[3]) :
      PowerSeries ℚ_[3])
  have hb0 : PowerSeries.constantCoeff b = 0 := by
    dsimp [b]
    rw [f3PadicLogMulPolynomial_toPowerSeries]
    simp
  have hzero :
      PowerSeries.coeff 0
        ((PowerSeries.log ℚ_[3]).subst b) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hb0,
      PowerSeries.constantCoeff_log]
    simp
  have hxlt : ‖x‖ < 1 := lt_of_le_of_lt hx (by norm_num)
  have hylt : ‖y‖ < 1 := lt_of_le_of_lt hy (by norm_num)
  have htail :
      HasSum
        (fun k : ℕ =>
          PowerSeries.coeff (k + 1)
            ((PowerSeries.log ℚ_[3]).subst b))
        (f3PadicLogOnePlus x + f3PadicLogOnePlus y) := by
    simpa [b, f3PadicLogMulPolynomial_toPowerSeries] using
      (hasSum_f3PadicFormal_log_mul_lhs_coeff hxlt hylt)
  have hall :
      HasSum
        (fun n : ℕ =>
          PowerSeries.coeff n
            ((PowerSeries.log ℚ_[3]).subst b))
        (f3PadicLogOnePlus x + f3PadicLogOnePlus y) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one, hzero] using htail
  have hout :=
    hasSum_f3PadicLogComposition_by_output hx hy hxy
  have hout' :
      HasSum
        (fun n : ℕ =>
          PowerSeries.coeff n
            ((PowerSeries.log ℚ_[3]).subst b))
        (f3PadicLogOnePlus (x + y + x * y)) := by
    refine hout.congr fun n => ?_
    dsimp [b]
    exact f3PadicLogComposition_output_fiber_tsum_eq_coeff x y n
  exact hout'.unique hall

/-- The genuine F₃ 3-adic logarithmic coordinate is multiplicative-to-additive
on its natural domain. -/
theorem f3PadicLog_mul
    {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3PadicLog (m * n) = f3PadicLog m + f3PadicLog n := by
  have hx :
      ‖f3PadicDelta m‖ ≤ (1 / 3 : ℝ) := by
    simpa [one_div] using f3PadicDelta_norm_le_one_third hm hm3
  have hy :
      ‖f3PadicDelta n‖ ≤ (1 / 3 : ℝ) := by
    simpa [one_div] using f3PadicDelta_norm_le_one_third hn hn3
  have hxy :=
    f3PadicDelta_mul_norm_lt_one hm hn hm3 hn3
  rw [f3PadicLog_mul_reduction hm3 hn3]
  simpa [f3PadicLog] using
    (f3PadicLogOnePlus_product hx hy hxy)

end OmegaBalance
