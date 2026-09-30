import OmegaBalance.F3PadicLogCompositionCoeff

/-!
# Output-fiber coefficient identification

This module identifies each output-degree fiber of the already-summable
triangular composition family with the corresponding coefficient of the
formal power-series substitution.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The output-degree fiber of the triangular index set is naturally the set
of outer degrees whose polynomial power can still reach that output degree. -/
def f3PadicLogCompositionOutputFiberEquiv (n : ℕ) :
    {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n} ≃
      {d : ℕ // n < 2 * d + 1} where
  toFun p := ⟨p.1.1, by
    simpa [p.2] using p.1.2.2⟩
  invFun d := ⟨⟨d.1, ⟨n, d.2⟩⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨d, ⟨v, hv⟩⟩, h⟩
    change v = n at h
    subst v
    rfl
  right_inv d := by
    rcases d with ⟨d, hd⟩
    rfl

/-- The sum over one output-degree fiber equals the unrestricted outer-degree
sum: terms outside the fiber vanish by the explicit degree bound
`deg(P^d) ≤ 2d`. -/
theorem f3PadicLogComposition_output_fiber_tsum_eq_full
    (x y : ℚ_[3]) (n : ℕ) :
    (∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
      PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ p.1.1).coeff p.1.2) =
      ∑' d : ℕ,
        PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
          (f3PadicLogMulPolynomial x y ^ d).coeff n := by
  let e := f3PadicLogCompositionOutputFiberEquiv n
  calc
    (∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
      PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ p.1.1).coeff p.1.2)
        =
      ∑' d : {d : ℕ // n < 2 * d + 1},
        PowerSeries.coeff d.1 (PowerSeries.log ℚ_[3]) *
          (f3PadicLogMulPolynomial x y ^ d.1).coeff n := by
            rw [← e.tsum_eq]
            apply tsum_congr
            intro p
            dsimp [e, f3PadicLogCompositionOutputFiberEquiv]
            exact congrArg
              (fun k : ℕ =>
                PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
                  (f3PadicLogMulPolynomial x y ^ p.1.1).coeff k)
              p.2
    _ =
      ∑' d : ℕ,
        PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
          (f3PadicLogMulPolynomial x y ^ d).coeff n := by
            refine tsum_subtype_eq_of_support_subset
              (f := fun d : ℕ =>
                PowerSeries.coeff d (PowerSeries.log ℚ_[3]) *
                  (f3PadicLogMulPolynomial x y ^ d).coeff n)
              (s := {d : ℕ | n < 2 * d + 1}) ?_
            intro d hd
            change n < 2 * d + 1
            by_contra hdn
            have htwo : 2 * d < n := by omega
            have hz :=
              f3PadicLogMulPolynomial_pow_coeff_eq_zero_of_two_mul_lt
                x y htwo
            exact hd (by simp [hz])

/-- Each justified output-degree fiber is exactly the matching coefficient of
the formal logarithm substituted into the quadratic product increment. -/
theorem f3PadicLogComposition_output_fiber_tsum_eq_coeff
    (x y : ℚ_[3]) (n : ℕ) :
    (∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
      PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
        (f3PadicLogMulPolynomial x y ^ p.1.1).coeff p.1.2) =
      PowerSeries.coeff n
        ((PowerSeries.log ℚ_[3]).subst
          ((f3PadicLogMulPolynomial x y : Polynomial ℚ_[3]) :
            PowerSeries ℚ_[3])) := by
  rw [f3PadicLogComposition_output_fiber_tsum_eq_full,
    f3PadicLogComposition_coeff_tsum_eq]

end OmegaBalance
