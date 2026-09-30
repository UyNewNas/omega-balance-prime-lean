import OmegaBalance.F3PrimeDensityTail

/-!
# Exact relative densities among all primes

The existing AP-PNT consequences normalize counts by `x / log x`.
Specializing that same proved theorem to modulus one makes the denominator
here the actual count of all primes, not an asymptotic substitute.
All exceptional finite initial values use the ordinary totalized real quotient.
-/

open Filter Topology

namespace OmegaBalance

/-- The number of all primes at most the nonnegative floor of `x`. -/
noncomputable def f3AllPrimeCountingReal (x : ℝ) : ℝ :=
  (((Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime).card : ℝ)

/-- Modulus one and residue zero impose no additional restriction on primes. -/
theorem f3AllPrimeCountingReal_eq_AP (x : ℝ) :
    f3AllPrimeCountingReal x = f3PrimeAPCountingReal 1 0 x := by
  simp only [f3AllPrimeCountingReal, f3PrimeAPCountingReal, Nat.mod_one, and_true]

/-- The denominator asymptotic is the proved AP-PNT at modulus one. -/
theorem f3AllPrimeCountingReal_normalized_tendsto :
    Tendsto (fun x : ℝ => f3AllPrimeCountingReal x / (x / Real.log x))
      atTop (𝓝 1) := by
  simpa only [f3AllPrimeCountingReal_eq_AP, Nat.totient_one, Nat.cast_one, inv_one]
    using (f3PrimeAPCountingReal_normalized_tendsto
      (A := 1) (a := 0) (by decide) (by decide) (by decide))

/-- In particular, the actual all-prime denominator is eventually nonzero. -/
theorem eventually_f3AllPrimeCountingReal_ne_zero :
    ∀ᶠ x : ℝ in atTop, f3AllPrimeCountingReal x ≠ 0 := by
  have h := f3AllPrimeCountingReal_normalized_tendsto.eventually_ne
    (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [h] with x hx
  intro hz
  apply hx
  simp [hz]

/-- Transfer an `x/log x` counting limit to an actual proportion of all primes.
The denominator limit is proved above, rather than assumed. -/
theorem f3PrimeRelativeLimit_of_normalized {f : ℝ → ℝ} {a : ℝ}
    (hf : Tendsto (fun x : ℝ => f x / (x / Real.log x)) atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => f x / f3AllPrimeCountingReal x) atTop (𝓝 a) := by
  have hden := f3AllPrimeCountingReal_normalized_tendsto
  have hratio : Tendsto
      (fun x : ℝ => (f x / (x / Real.log x)) /
        (f3AllPrimeCountingReal x / (x / Real.log x)))
      atTop (𝓝 a) := by
    convert hf.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  refine hratio.congr' ?_
  have hne := hden.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [hne] with x hx
  have hscale : x / Real.log x ≠ 0 := by
    intro hz
    apply hx
    simp [hz]
  exact div_div_div_cancel_right₀ hscale (f x) (f3AllPrimeCountingReal x)

/-- Each fixed positive exact F₃ level has proportion `3⁻ᵏ` among all primes. -/
theorem f3PrimePosLevel_relative_density {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => f3PrimePosLevelCountingReal k x /
      f3AllPrimeCountingReal x) atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  exact f3PrimeRelativeLimit_of_normalized
    (f3PrimePosLevelCountingReal_normalized_tendsto hk)

/-- Each fixed negative exact F₃ level has the same actual prime proportion. -/
theorem f3PrimeNegLevel_relative_density {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => f3PrimeNegLevelCountingReal k x /
      f3AllPrimeCountingReal x) atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  exact f3PrimeRelativeLimit_of_normalized
    (f3PrimeNegLevelCountingReal_normalized_tendsto hk)

/-- The actual prime proportion of depth at least `K>0` is `3^(1-K)`. -/
theorem f3PrimeTail_relative_density {K : ℕ} (hK : 0 < K) :
    Tendsto (fun x : ℝ => f3PrimeTailCountingReal K x /
      f3AllPrimeCountingReal x) atTop (𝓝 (1 / (3 : ℝ) ^ (K - 1))) := by
  exact f3PrimeRelativeLimit_of_normalized
    (f3PrimeTailCountingReal_normalized_tendsto hK)

end OmegaBalance
