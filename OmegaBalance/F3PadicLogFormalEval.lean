import OmegaBalance.F3PadicLogFormalMul

/-!
# Coefficient-sum specialization of the formal 3-adic logarithm law

This module specializes the exact formal group law to the linear series
`x * X` and `y * X`, then connects the two rescaled logarithm series to
the genuine convergent `ℚ_[3]` logarithm sums already defined in
`F3PadicLog.lean`.

It deliberately stops short of the final composition/evaluation step:
identifying the coefficient sum of
`log.subst (x*X + y*X + xy*X^2)` with the direct analytic series at
`x + y + xy` still requires a justified summation interchange.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Specialize the formal multiplicative logarithm law to the linear series
`x • X` and `y • X`.  The two right-hand substitutions are rewritten as
ordinary rescalings, whose coefficients can be evaluated directly. -/
theorem f3PadicFormal_log_mul_rescale (x y : ℚ_[3]) :
    (PowerSeries.log ℚ_[3]).subst
        ((x • PowerSeries.X : PowerSeries ℚ_[3]) +
          (y • PowerSeries.X : PowerSeries ℚ_[3]) +
          (x • PowerSeries.X : PowerSeries ℚ_[3]) *
            (y • PowerSeries.X : PowerSeries ℚ_[3])) =
      PowerSeries.rescale x (PowerSeries.log ℚ_[3]) +
        PowerSeries.rescale y (PowerSeries.log ℚ_[3]) := by
  have hx :
      PowerSeries.constantCoeff
          (x • PowerSeries.X : PowerSeries ℚ_[3]) = 0 := by
    simp
  have hy :
      PowerSeries.constantCoeff
          (y • PowerSeries.X : PowerSeries ℚ_[3]) = 0 := by
    simp
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  exact f3PadicFormal_log_mul
    (x • PowerSeries.X : PowerSeries ℚ_[3])
    (y • PowerSeries.X : PowerSeries ℚ_[3]) hx hy

/-- The positive-degree coefficients of the rescaled formal logarithm at
`x` sum to the genuine analytic logarithm `f3PadicLogOnePlus x` whenever
`x` lies in the open 3-adic unit ball. -/
theorem hasSum_f3PadicLog_rescale_coeff {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          (PowerSeries.rescale x (PowerSeries.log ℚ_[3])))
      (f3PadicLogOnePlus x) := by
  simpa [PowerSeries.coeff_rescale, mul_comm] using
    (hasSum_f3PadicLog_powerSeries_coeff hx)

/-- The coefficientwise sum on the right side of the specialized formal
multiplication law converges to the sum of the two genuine 3-adic logs. -/
theorem hasSum_f3PadicFormal_log_mul_rhs_coeff
    {x y : ℚ_[3]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          (PowerSeries.rescale x (PowerSeries.log ℚ_[3]) +
            PowerSeries.rescale y (PowerSeries.log ℚ_[3])))
      (f3PadicLogOnePlus x + f3PadicLogOnePlus y) := by
  have h :=
    (hasSum_f3PadicLog_rescale_coeff hx).add
      (hasSum_f3PadicLog_rescale_coeff hy)
  simpa using h

/-- Consequently the positive-degree coefficients of the *formal product
logarithm* have a genuine convergent sum, namely the sum of the two analytic
logs.  This is the exact formal-to-analytic coefficient bridge immediately
before the remaining composition/evaluation interchange. -/
theorem hasSum_f3PadicFormal_log_mul_lhs_coeff
    {x y : ℚ_[3]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum
      (fun k : ℕ =>
        PowerSeries.coeff (k + 1)
          ((PowerSeries.log ℚ_[3]).subst
            ((x • PowerSeries.X : PowerSeries ℚ_[3]) +
              (y • PowerSeries.X : PowerSeries ℚ_[3]) +
              (x • PowerSeries.X : PowerSeries ℚ_[3]) *
                (y • PowerSeries.X : PowerSeries ℚ_[3]))))
      (f3PadicLogOnePlus x + f3PadicLogOnePlus y) := by
  rw [f3PadicFormal_log_mul_rescale x y]
  exact hasSum_f3PadicFormal_log_mul_rhs_coeff hx hy

end OmegaBalance
