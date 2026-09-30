import OmegaBalance.F3PrimeDensityAPPartial

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma f3PrimeAPCountingReal_eq_thetaAP_div_log_add_integral
    (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    f3PrimeAPCountingReal A a x =
      f3ThetaAP A a x / Real.log x +
        ∫ t in 2..x, f3ThetaAP A a t / (t * Real.log t ^ 2) := by
  rw [f3PrimeAPCountingReal, Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  let b : ℕ → ℝ := Set.indicator
    {n : ℕ | n.Prime ∧ n % A = a} (fun n => Real.log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * b n
  · refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h
    · have hnlog : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.1.pos) (mod_cast h.1.ne_one)
      simp [b, h, hnlog]
    · simp [b, h]
  rw [sum_mul_eq_sub_integral_mul₁ b (f := fun n => (Real.log n)⁻¹)
      (by simp [b]) (by simp [b]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun y => (Real.log y)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * Real.log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by
        simp [Real.deriv_inv_log, field]
    simp [-Real.deriv_inv_log, int_deriv, b, Set.indicator_apply, Finset.sum_filter, f3ThetaAP]
    grind
  · intro z ⟨hz, _⟩
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop (disch := assumption)
  · refine ContinuousOn.integrableOn_Icc fun z ⟨hz, _⟩ =>
      ContinuousWithinAt.congr ?_ (fun _ _ => Real.deriv_inv_log_apply)
        Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith
    have hzlog : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by
      fun_prop (disch := assumption)

end OmegaBalance
