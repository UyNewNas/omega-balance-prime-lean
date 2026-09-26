import OmegaBalance.F3PrimeDensityAPTail

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma f3ThetaAP_asymptotic {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    f3ThetaAP A a ~[atTop] (fun x : ℝ => x / A.totient) := by
  simpa only [f3ThetaAP] using! chebyshev_asymptotic_pnt hA ha haA

lemma f3ThetaAP_div_id_tendsto {A a : ℕ} (hA : 0 < A) (ha : a.Coprime A)
    (haA : a < A) :
    Tendsto (fun x : ℝ => f3ThetaAP A a x / x) atTop
      (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have htot : (A.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hA).ne'
  have hden : ∀ᶠ x : ℝ in atTop, x / (A.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx htot
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
    (f3ThetaAP_asymptotic hA ha haA)
  convert h.div_const (A.totient : ℝ) using 1
  · funext x
    simp only [Pi.div_apply]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  · field_simp

theorem f3PrimeAPCountingReal_normalized_tendsto {A a : ℕ}
    (hA : 0 < A) (ha : a.Coprime A) (haA : a < A) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeAPCountingReal A a x / (x / Real.log x))
      atTop (𝓝 ((A.totient : ℝ)⁻¹)) := by
  have hint := (f3Integral_thetaAP_div_log_sq_isLittleO A a).tendsto_div_nhds_zero
  have hsum := (f3ThetaAP_div_id_tendsto hA ha haA).add hint
  simpa only [add_zero] using hsum.congr' <| by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [f3PrimeAPCountingReal_eq_thetaAP_div_log_add_integral A a hx]
    have hx0 : x ≠ 0 := by linarith
    have hlog : Real.log x ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field


/-- The nested arithmetic-progression count for the exact negative F₃ level.
For primes above three, the residue condition `p ≡ 1 [MOD 3^k]` is exactly
`k ≤ v₃(p-1)`; subtracting the next modulus isolates valuation exactly `k`. -/
noncomputable def f3PrimeNegLevelAPDifference (k : ℕ) (x : ℝ) : ℝ :=
  f3PrimeAPCountingReal (3 ^ k) 1 x -
    f3PrimeAPCountingReal (3 ^ (k + 1)) 1 x

/-- Before simplifying Euler totients, the exact negative-level AP proxy has
the expected difference of the two fixed-residue PNT-AP constants. -/
theorem f3PrimeNegLevelAPDifference_normalized_tendsto_totient
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeNegLevelAPDifference k x / (x / Real.log x))
      atTop
      (𝓝 (((Nat.totient (3 ^ k) : ℝ)⁻¹) -
        ((Nat.totient (3 ^ (k + 1)) : ℝ)⁻¹))) := by
  have hklt : 1 < 3 ^ k :=
    Nat.one_lt_pow hk.ne' (by norm_num : 1 < (3 : ℕ))
  have hkslt : 1 < 3 ^ (k + 1) :=
    Nat.one_lt_pow (by omega : k + 1 ≠ 0) (by norm_num : 1 < (3 : ℕ))
  have h0 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ k) (a := 1)
      (by positivity) (by simp) hklt
  have h1 :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 3 ^ (k + 1)) (a := 1)
      (by positivity) (by simp) hkslt
  simpa [f3PrimeNegLevelAPDifference, sub_div] using h0.sub h1


/-- Euler's totient constants for two successive powers of three differ by
exactly the density constant `3⁻ᵏ`. -/
lemma f3_totient_three_pow_inv_sub_succ
    {k : ℕ} (hk : 0 < k) :
    ((Nat.totient (3 ^ k) : ℝ)⁻¹) -
        ((Nat.totient (3 ^ (k + 1)) : ℝ)⁻¹) =
      1 / (3 : ℝ) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.totient_prime_pow Nat.prime_three (by omega : 0 < j + 1)]
  rw [Nat.totient_prime_pow Nat.prime_three (by omega : 0 < (j + 1) + 1)]
  norm_num [Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

/-- The exact negative-level AP proxy therefore has normalized density `3⁻ᵏ`. -/
theorem f3PrimeNegLevelAPDifference_normalized_tendsto
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun x : ℝ =>
        f3PrimeNegLevelAPDifference k x / (x / Real.log x))
      atTop (𝓝 (1 / (3 : ℝ) ^ k)) := by
  simpa [f3_totient_three_pow_inv_sub_succ hk] using
    f3PrimeNegLevelAPDifference_normalized_tendsto_totient hk

end OmegaBalance
