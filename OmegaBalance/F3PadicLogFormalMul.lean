import OmegaBalance.F3PadicLogMulDefectContraction

/-!
# Formal multiplicative law for the 3-adic logarithm

This module proves the formal power-series group law underlying LOG-1.
It does not yet identify this formal identity with the analytic sum
`f3PadicLog`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Chain-rule form of the formal identity
`(log(1+f))' * (1+f) = f'` for a zero-constant-term series `f`. -/
theorem f3PadicFormal_log_derivative_mul_one_add
    (f : (ℚ_[3])⟦X⟧) (hf : PowerSeries.constantCoeff f = 0) :
    d⁄dX ((PowerSeries.log ℚ_[3]).subst f) * (1 + f) = d⁄dX f := by
  have hs : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf
  rw [PowerSeries.derivative_subst hs]
  have hlog :
      (d⁄dX (PowerSeries.log ℚ_[3])).subst f * (1 + f) = 1 := by
    calc
      (d⁄dX (PowerSeries.log ℚ_[3])).subst f * (1 + f)
          =
          ((d⁄dX (PowerSeries.log ℚ_[3])) *
            (1 + PowerSeries.X)).subst f := by
              rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs,
                PowerSeries.subst_X hs]
              simp
      _ = (1 : (ℚ_[3])⟦X⟧).subst f := by
            rw [PowerSeries.derivative_log_mul_one_add_X]
      _ = 1 := by simp
  calc
    ((d⁄dX (PowerSeries.log ℚ_[3])).subst f * d⁄dX f) * (1 + f)
        =
        ((d⁄dX (PowerSeries.log ℚ_[3])).subst f * (1 + f)) *
          d⁄dX f := by ring
    _ = d⁄dX f := by rw [hlog, one_mul]

/-- Purely formal logarithm group law:
`log(1 + f + g + fg) = log(1+f) + log(1+g)`.
This is the exact algebraic identity needed before the analytic evaluation
step in LOG-1. -/
theorem f3PadicFormal_log_mul
    (f g : (ℚ_[3])⟦X⟧)
    (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.log ℚ_[3]).subst (f + g + f * g) =
      (PowerSeries.log ℚ_[3]).subst f +
        (PowerSeries.log ℚ_[3]).subst g := by
  let h : (ℚ_[3])⟦X⟧ := f + g + f * g
  have hh : PowerSeries.constantCoeff h = 0 := by
    dsimp [h]
    simp [hf, hg]
  have hunit : IsUnit (1 + h) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [hh]
  have hmain :=
    f3PadicFormal_log_derivative_mul_one_add h hh
  have hfmain :=
    f3PadicFormal_log_derivative_mul_one_add f hf
  have hgmain :=
    f3PadicFormal_log_derivative_mul_one_add g hg
  have hfactor : 1 + h = (1 + f) * (1 + g) := by
    dsimp [h]
    ring
  have hderiv :
      d⁄dX h = (d⁄dX f) * (1 + g) + (d⁄dX g) * (1 + f) := by
    dsimp [h]
    simp only [map_add, Derivation.leibniz]
    ring
  have hrhs :
      d⁄dX ((PowerSeries.log ℚ_[3]).subst f +
          (PowerSeries.log ℚ_[3]).subst g) * (1 + h) =
        d⁄dX h := by
    rw [map_add, hfactor]
    calc
      (d⁄dX ((PowerSeries.log ℚ_[3]).subst f) +
          d⁄dX ((PowerSeries.log ℚ_[3]).subst g)) *
            ((1 + f) * (1 + g))
          =
          (d⁄dX ((PowerSeries.log ℚ_[3]).subst f) * (1 + f)) *
              (1 + g) +
            (d⁄dX ((PowerSeries.log ℚ_[3]).subst g) * (1 + g)) *
              (1 + f) := by ring
      _ = (d⁄dX f) * (1 + g) + (d⁄dX g) * (1 + f) := by
            rw [hfmain, hgmain]
      _ = d⁄dX h := hderiv.symm
  change (PowerSeries.log ℚ_[3]).subst h =
      (PowerSeries.log ℚ_[3]).subst f +
        (PowerSeries.log ℚ_[3]).subst g
  apply PowerSeries.derivative.ext
  · apply mul_right_cancel₀ hunit.ne_zero
    rw [hmain, hrhs]
  · simp [PowerSeries.constantCoeff_subst_of_constantCoeff_zero, hh, hf, hg]

end OmegaBalance
