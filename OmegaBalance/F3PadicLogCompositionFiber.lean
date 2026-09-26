import OmegaBalance.F3PadicLogCompositionMajorant

/-!
# Fiberwise regrouping for the 3-adic logarithm composition series

The coefficient majorant from `F3PadicLogCompositionMajorant` makes the
outer-degree / inner-coefficient family summable.  This file performs the
first exact regrouping: for every fixed outer logarithm degree `d`, the
finite inner coefficient fiber sums to the direct monomial
`coeff_d(log) * (x + y + x*y)^d`.

This is a genuine analytic input toward the final identity
`L(m*n)=L(m)+L(n)`; it does not assume that identity.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Summing the whole explicit coefficient range of the `d`-th product
polynomial power recovers its evaluation at one, hence the direct product
increment raised to `d`. -/
theorem f3PadicLogComposition_range_fiber_sum
    (x y : ℚ_[3]) (d : ℕ) :
    (∑ n ∈ Finset.range (2 * d + 1),
      PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ d).coeff n) =
      PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (x + y + x * y) ^ d := by
  rw [← Finset.mul_sum]
  have hdeg :
      (f3PadicLogMulPolynomial x y ^ d).natDegree < 2 * d + 1 :=
    lt_of_le_of_lt
      (f3PadicLogMulPolynomial_pow_natDegree_le x y d) (by omega)
  have heval :=
    Polynomial.eval_eq_sum_range'
      (p := f3PadicLogMulPolynomial x y ^ d)
      hdeg (1 : ℚ_[3])
  simp only [one_pow, mul_one] at heval
  rw [← heval, Polynomial.eval_pow, f3PadicLogMulPolynomial_eval_one]

/-- Same fiber identity on the dependent finite type used by the global
summability theorem. -/
theorem f3PadicLogComposition_fin_fiber_sum
    (x y : ℚ_[3]) (d : ℕ) :
    (∑ n : Fin (2 * d + 1),
      PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ d).coeff n) =
      PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
        (x + y + x * y) ^ d := by
  simpa only [← Fin.sum_univ_eq_sum_range] using
    (f3PadicLogComposition_range_fiber_sum x y d)

/-- The sequence of exact finite fibers has the direct analytic logarithm as
its sum whenever the nonlinear product increment lies in the open unit ball. -/
theorem hasSum_f3PadicLogComposition_fibers
    {x y : ℚ_[3]} (hxy : ‖x + y + x * y‖ < 1) :
    HasSum
      (fun d : ℕ =>
        ∑ n : Fin (2 * d + 1),
          PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
            (f3PadicLogMulPolynomial x y ^ d).coeff n)
      (f3PadicLogOnePlus (x + y + x * y)) := by
  simpa only [f3PadicLogComposition_fin_fiber_sum] using
    (hasSum_f3PadicLog_all_coeff hxy)

/-- Fubini in the already-proved absolutely summable triangular family:
the total supported coefficient sum is exactly the direct analytic
logarithm of the nonlinear product increment. -/
theorem f3PadicLogComposition_supported_tsum_eq
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (hxy : ‖x + y + x * y‖ < 1) :
    (∑' p : Σ d : ℕ, Fin (2 * d + 1),
      PowerSeries.coeff p.1 (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ p.1).coeff p.2) =
      f3PadicLogOnePlus (x + y + x * y) := by
  have hs := summable_f3PadicLogComposition_supported_terms hx hy
  calc
    (∑' p : Σ d : ℕ, Fin (2 * d + 1),
      PowerSeries.coeff p.1 (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ p.1).coeff p.2) =
        ∑' d : ℕ, ∑' n : Fin (2 * d + 1),
          PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
            (f3PadicLogMulPolynomial x y ^ d).coeff n := by
              exact hs.tsum_sigma' (fun _ => Summable.of_finite)
    _ = ∑' d : ℕ,
        PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
          (x + y + x * y) ^ d := by
          congr 1
          funext d
          rw [tsum_fintype]
          exact f3PadicLogComposition_fin_fiber_sum x y d
    _ = f3PadicLogOnePlus (x + y + x * y) :=
      (hasSum_f3PadicLog_all_coeff hxy).tsum_eq

end OmegaBalance
