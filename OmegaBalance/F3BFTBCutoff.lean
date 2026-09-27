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

end OmegaBalance
