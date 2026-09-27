import OmegaBalance.F3PadicLogCompositionOutputFiber

/-!
# Coefficient identification for the 3-adic logarithm composition

This module identifies the full outer-degree sum contributing to a fixed
output coefficient with the corresponding coefficient of the exact formal
substitution.  The finite-support theorem behind `PowerSeries.coeff_subst'`
makes this a genuine finite-to-infinite-sum bridge rather than a formal
exchange of conditionally convergent series.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- For every output degree `n`, summing all outer logarithm degrees gives
exactly the `n`-th coefficient of the formal logarithm substituted into the
quadratic principal-unit product increment. -/
theorem f3PadicLogComposition_coeff_tsum_eq
    (x y : ℚ_[3]) (n : ℕ) :
    (∑' d : ℕ,
      PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ d).coeff n) =
      PowerSeries.coeff n
        ((PowerSeries.log ℚ_[3]).subst
          ((f3PadicLogMulPolynomial x y : Polynomial ℚ_[3]) :
            PowerSeries ℚ_[3])) := by
  let b : PowerSeries ℚ_[3] :=
    ((f3PadicLogMulPolynomial x y : Polynomial ℚ_[3]) :
      PowerSeries ℚ_[3])
  have hb0 : PowerSeries.constantCoeff b = 0 := by
    dsimp [b]
    simp [f3PadicLogMulPolynomial]
  have hb : PowerSeries.HasSubst b :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  have hfinite :=
    PowerSeries.coeff_subst_finite' hb (PowerSeries.log ℚ_[3]) n
  rw [PowerSeries.coeff_subst' hb]
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hfinite]
  congr 1
  funext d
  simp [b, ← Polynomial.coe_pow, smul_eq_mul]

end OmegaBalance
