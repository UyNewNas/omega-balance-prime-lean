import OmegaBalance.F3PadicLogFormalEval

/-!
# Finite polynomial layer for the final 3-adic logarithm composition bridge

The remaining analytic specialization of the formal logarithm law involves the
quadratic series `x*X + y*X + x*y*X^2`.

This file records that series as the image of an ordinary polynomial. Its
powers therefore have finite coefficient support, and the coefficient sum of
the `d`-th power is exactly `(x + y + x*y)^d`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Polynomial model of the principal-unit product increment. -/
noncomputable def f3PadicLogMulPolynomial (x y : ℚ_[3]) : Polynomial ℚ_[3] :=
  Polynomial.C x * Polynomial.X +
    Polynomial.C y * Polynomial.X +
    Polynomial.C (x * y) * Polynomial.X ^ 2

/-- Evaluation of the quadratic product polynomial at one. -/
theorem f3PadicLogMulPolynomial_eval_one (x y : ℚ_[3]) :
    (f3PadicLogMulPolynomial x y).eval 1 = x + y + x * y := by
  simp [f3PadicLogMulPolynomial]

/-- The polynomial model embeds into the exact quadratic power series used in
the specialized formal logarithm identity. -/
theorem f3PadicLogMulPolynomial_toPowerSeries (x y : ℚ_[3]) :
    ((f3PadicLogMulPolynomial x y : Polynomial ℚ_[3]) : PowerSeries ℚ_[3]) =
      (x • PowerSeries.X : PowerSeries ℚ_[3]) +
        (y • PowerSeries.X : PowerSeries ℚ_[3]) +
        (x • PowerSeries.X : PowerSeries ℚ_[3]) *
          (y • PowerSeries.X : PowerSeries ℚ_[3]) := by
  simp [f3PadicLogMulPolynomial, PowerSeries.smul_eq_C_mul]
  ring

/-- Finite coefficient evaluation for every outer logarithm degree. -/
theorem f3PadicLogMulPolynomial_pow_coeff_sum
    (x y : ℚ_[3]) (d : ℕ) :
    (∑ n ∈ (f3PadicLogMulPolynomial x y ^ d).support,
      (f3PadicLogMulPolynomial x y ^ d).coeff n) =
      (x + y + x * y) ^ d := by
  calc
    (∑ n ∈ (f3PadicLogMulPolynomial x y ^ d).support,
        (f3PadicLogMulPolynomial x y ^ d).coeff n) =
        (f3PadicLogMulPolynomial x y ^ d).eval 1 := by
          rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
          simp
    _ = (x + y + x * y) ^ d := by
      rw [Polynomial.eval_pow, f3PadicLogMulPolynomial_eval_one]

end OmegaBalance
