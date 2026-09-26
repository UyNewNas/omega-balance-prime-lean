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
    (f : PowerSeries ℚ_[3]) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst f) * (1 + f) = PowerSeries.derivative f := by
  have hs : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf
  rw [PowerSeries.derivative_subst hs]
  have hone : (1 : PowerSeries ℚ_[3]).subst f = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs, map_one]
  have hlog :
      (PowerSeries.derivative (PowerSeries.log ℚ_[3])).subst f * (1 + f) = 1 := by
    calc
      (PowerSeries.derivative (PowerSeries.log ℚ_[3])).subst f * (1 + f)
          =
          ((PowerSeries.derivative (PowerSeries.log ℚ_[3])) *
            (1 + PowerSeries.X)).subst f := by
              rw [PowerSeries.subst_mul hs, PowerSeries.subst_add hs,
                PowerSeries.subst_X hs, hone]
      _ = (1 : PowerSeries ℚ_[3]).subst f := by
            rw [PowerSeries.derivative_log_mul_one_add_X]
      _ = 1 := hone
  calc
    ((PowerSeries.derivative (PowerSeries.log ℚ_[3])).subst f * PowerSeries.derivative f) * (1 + f)
        =
        ((PowerSeries.derivative (PowerSeries.log ℚ_[3])).subst f * (1 + f)) *
          PowerSeries.derivative f := by ring
    _ = PowerSeries.derivative f := by rw [hlog, one_mul]

/-- Purely formal logarithm group law:
`log(1 + f + g + fg) = log(1+f) + log(1+g)`.
This is the exact algebraic identity needed before the analytic evaluation
step in LOG-1. -/
theorem f3PadicFormal_log_mul
    (f g : PowerSeries ℚ_[3])
    (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    (PowerSeries.log ℚ_[3]).subst (f + g + f * g) =
      (PowerSeries.log ℚ_[3]).subst f +
        (PowerSeries.log ℚ_[3]).subst g := by
  let h : PowerSeries ℚ_[3] := f + g + f * g
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
      PowerSeries.derivative h = (PowerSeries.derivative f) * (1 + g) + (PowerSeries.derivative g) * (1 + f) := by
    dsimp [h]
    simp only [map_add, Derivation.leibniz]
    ring
  have hrhs :
      PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst f +
          (PowerSeries.log ℚ_[3]).subst g) * (1 + h) =
        PowerSeries.derivative h := by
    rw [map_add, hfactor]
    calc
      (PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst f) +
          PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst g)) *
            ((1 + f) * (1 + g))
          =
          (PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst f) * (1 + f)) *
              (1 + g) +
            (PowerSeries.derivative ((PowerSeries.log ℚ_[3]).subst g) * (1 + g)) *
              (1 + f) := by ring
      _ = (PowerSeries.derivative f) * (1 + g) + (PowerSeries.derivative g) * (1 + f) := by
            rw [hfmain, hgmain]
      _ = PowerSeries.derivative h := hderiv.symm
  change (PowerSeries.log ℚ_[3]).subst h =
      (PowerSeries.log ℚ_[3]).subst f +
        (PowerSeries.log ℚ_[3]).subst g
  apply PowerSeries.derivative.ext
  · apply mul_right_cancel₀ hunit.ne_zero
    rw [hmain, hrhs]
  · simp only [PowerSeries.constantCoeff_eq, map_add]
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hh,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hf,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hg]
    simp

end OmegaBalance
