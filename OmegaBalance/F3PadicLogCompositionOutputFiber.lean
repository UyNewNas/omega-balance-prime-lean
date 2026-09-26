import OmegaBalance.F3PadicLogCompositionFiber

/-!
# Output-degree regrouping for the 3-adic logarithm composition series

The triangular double series has already been proved summable and its total
sum identified with the direct analytic logarithm.  Here we regroup that same
summable family by the output coefficient degree.  This is the second Fubini
orientation needed to compare the analytic composition with the formal
substitution coefficients.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
attribute [local instance 1001] Ring.toAddCommGroup AddCommGroup.toAddCommMonoid

/-- Regroup the absolutely summable composition family by its output
coefficient degree.  No coefficient identification is used here; this is
purely the justified Fubini/fiberwise reindexing step. -/
theorem hasSum_f3PadicLogComposition_by_output
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (hxy : ‖x + y + x * y‖ < 1) :
    HasSum
      (fun n : ℕ =>
        ∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
          PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
            (f3PadicLogMulPolynomial x y ^ p.1.1).coeff p.1.2)
      (f3PadicLogOnePlus (x + y + x * y)) := by
  let F : (Σ d : ℕ, Fin (2 * d + 1)) → ℚ_[3] := fun p =>
    PowerSeries.coeff p.1 (PowerSeries.log ℚ_[3]) *
      (f3PadicLogMulPolynomial x y ^ p.1).coeff p.2
  have hs : Summable F :=
    summable_f3PadicLogComposition_supported_terms hx hy
  have htotal :
      HasSum F (f3PadicLogOnePlus (x + y + x * y)) := by
    rw [← f3PadicLogComposition_supported_tsum_eq hx hy hxy]
    exact hs.hasSum
  have hfib := htotal.tsum_fiberwise (fun p => p.2.1)
  refine hfib.congr fun n => ?_
  let e :
      ↑((fun p : (Σ d : ℕ, Fin (2 * d + 1)) => p.2.1) ⁻¹'
        ({n} : Set ℕ)) ≃
        {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n} where
    toFun p := ⟨p.1, by simpa using p.2⟩
    invFun p := ⟨p.1, by simpa using p.2⟩
    left_inv p := by rfl
    right_inv p := by rfl
  calc
    (∑' b : ↑((fun p : (Σ d : ℕ, Fin (2 * d + 1)) => p.2.1) ⁻¹'
        ({n} : Set ℕ)), F b) =
        ∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
          F p := by
            rw [← e.tsum_eq]
            apply tsum_congr
            intro p
            rfl
    _ = ∑' p : {p : Σ d : ℕ, Fin (2 * d + 1) // p.2.1 = n},
        PowerSeries.coeff p.1.1 (PowerSeries.log ℚ_[3]) *
          (f3PadicLogMulPolynomial x y ^ p.1.1).coeff p.1.2 := by
            apply tsum_congr
            intro p
            rfl

end OmegaBalance
