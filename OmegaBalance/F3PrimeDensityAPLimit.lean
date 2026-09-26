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

end OmegaBalance
