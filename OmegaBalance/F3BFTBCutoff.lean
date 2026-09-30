import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OmegaBalance

open Filter Topology Real

theorem bftb_tendsto_pow_log_div_rpow (m : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log x ^ m / x ^ b) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun y : ℝ => Real.log y ^ m / (1 * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero
  simp only [one_mul, add_zero] at hbase
  have hcomp :
      Tendsto (fun x : ℝ => Real.log (x ^ b) ^ m / (x ^ b)) atTop (𝓝 0) :=
    hbase.comp (tendsto_rpow_atTop hb)
  have hscaled :
      Tendsto
        (fun x : ℝ => b ^ m * (Real.log x ^ m / x ^ b))
        atTop (𝓝 0) :=
    hcomp.congr' <| by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.log_rpow hx, mul_pow]
      ring
  have hunscale :
      Tendsto
        (fun x : ℝ => (b ^ m)⁻¹ *
          (b ^ m * (Real.log x ^ m / x ^ b)))
        atTop (𝓝 0) := by
    simpa using hscaled.const_mul ((b ^ m)⁻¹)
  exact hunscale.congr fun x => by
    have hbm : b ^ m ≠ 0 := pow_ne_zero _ hb.ne'
    field_simp [hbm]

theorem bftb_eventually_pow_log_le_rpow (m : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ m ≤ x ^ b := by
  have hlt :
      ∀ᶠ x : ℝ in atTop, Real.log x ^ m / x ^ b < 1 := by
    simpa using
      (bftb_tendsto_pow_log_div_rpow m b hb).eventually
        (eventually_lt_nhds zero_lt_one)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hrpow : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  simpa only [one_mul] using ((div_lt_iff₀ hrpow).mp hx).le

theorem bftb_eventually_rpow_le_half_rpow_div_pow_log
    (B : ℕ) (θ : ℝ) (hθ : θ < (1 / 2 : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      x ^ θ ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := by
  have hb : 0 < (1 / 2 : ℝ) - θ := sub_pos.mpr hθ
  filter_upwards
    [bftb_eventually_pow_log_le_rpow B ((1 / 2 : ℝ) - θ) hb,
      eventually_gt_atTop (2 : ℝ)]
    with x hlog hx
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  rw [le_div_iff₀ (pow_pos hlog0 B)]
  calc
    x ^ θ * Real.log x ^ B
        ≤ x ^ θ * x ^ ((1 / 2 : ℝ) - θ) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le θ)
    _ = x ^ (θ + ((1 / 2 : ℝ) - θ)) := by
      rw [Real.rpow_add hx0]
    _ = x ^ (1 / 2 : ℝ) := by
      ring_nf

theorem bftb_eventually_floor_rpow_le_floor_half_rpow_div_pow_log
    (B : ℕ) (θ : ℝ) (hθ : θ < (1 / 2 : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      ⌊(N : ℝ) ^ θ⌋₊ ≤
        ⌊(N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B⌋₊ := by
  exact
    (tendsto_natCast_atTop_atTop.eventually
      (bftb_eventually_rpow_le_half_rpow_div_pow_log B θ hθ)).mono
      (fun _ h => Nat.floor_mono h)


/--
Real-exponent logarithmic loss estimate matching the Liu--Wang
`StandardBombieriVinogradov` parameter `B : ℝ`.
-/
theorem bftb_eventually_log_rpow_le_rpow
    (B b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ B ≤ x ^ b := by
  obtain ⟨m, hm⟩ :=
    archimedean_iff_nat_lt.1 Real.instArchimedean B
  have hlog :
      ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards
    [bftb_eventually_pow_log_le_rpow m b hb, hlog]
    with x hpow hxlog
  calc
    Real.log x ^ B ≤ Real.log x ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hxlog hm.le
    _ = Real.log x ^ m := by rw [Real.rpow_natCast]
    _ ≤ x ^ b := hpow

/--
For every fixed real logarithmic-loss exponent `B` and every
`θ < 1/2`, the power cutoff is eventually contained in the Liu--Wang
Pan cutoff before flooring.
-/
theorem bftb_eventually_rpow_le_half_rpow_div_rpow_log
    (B θ : ℝ) (hθ : θ < (1 / 2 : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      x ^ θ ≤ x ^ (1 / 2 : ℝ) / Real.log x ^ B := by
  have hb : 0 < (1 / 2 : ℝ) - θ := sub_pos.mpr hθ
  filter_upwards
    [bftb_eventually_log_rpow_le_rpow B ((1 / 2 : ℝ) - θ) hb,
      eventually_gt_atTop (1 : ℝ)]
    with x hlog hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog0 : 0 < Real.log x := Real.log_pos hx
  have hden : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlog0 B
  rw [le_div_iff₀ hden]
  calc
    x ^ θ * Real.log x ^ B
        ≤ x ^ θ * x ^ ((1 / 2 : ℝ) - θ) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le θ)
    _ = x ^ (θ + ((1 / 2 : ℝ) - θ)) := by
      rw [Real.rpow_add hx0]
    _ = x ^ (1 / 2 : ℝ) := by
      ring_nf

/-- Floored real-exponent cutoff inclusion matching Liu--Wang's Pan cutoff. -/
theorem bftb_eventually_floor_rpow_le_floor_half_rpow_div_rpow_log
    (B θ : ℝ) (hθ : θ < (1 / 2 : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      ⌊(N : ℝ) ^ θ⌋₊ ≤
        ⌊(N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B⌋₊ := by
  exact
    (tendsto_natCast_atTop_atTop.eventually
      (bftb_eventually_rpow_le_half_rpow_div_rpow_log B θ hθ)).mono
      (fun _ h => Nat.floor_mono h)

end OmegaBalance
