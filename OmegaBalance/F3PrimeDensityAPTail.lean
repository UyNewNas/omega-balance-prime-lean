import OmegaBalance.F3PrimeDensityAPAbel

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma f3ThetaAP_le_theta (A a : ℕ) (x : ℝ) :
    f3ThetaAP A a x ≤ Chebyshev.theta x := by
  rw [f3ThetaAP, Chebyshev.theta_eq_sum_Icc]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · exact le_rfl
  · exact Real.log_nonneg <| by
      have hprime := (Finset.mem_filter.mp hp).2
      exact_mod_cast hprime.one_lt.le

lemma f3Integral_thetaAP_div_log_sq_isLittleO (A a : ℕ) :
    (fun x => ∫ t in 2..x, f3ThetaAP A a t / (t * Real.log t ^ 2))
      =o[atTop] (fun x => x / Real.log x) := by
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO
    Chebyshev.integral_theta_div_log_sq_isLittleO
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hapInt : IntervalIntegrable
      (fun t => f3ThetaAP A a t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (f3IntegrableOn_thetaAP_div_id_mul_log_sq A a x)
  have hthetaInt : IntervalIntegrable
      (fun t => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hapNonneg :
      0 ≤ ∫ t in 2..x, f3ThetaAP A a t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (f3ThetaAP_nonneg A a t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  have hthetaNonneg :
      0 ≤ ∫ t in 2..x, Chebyshev.theta t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      exact div_nonneg (Chebyshev.theta_nonneg t) <| mul_nonneg
        (by linarith [ht.1]) (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hapNonneg,
    abs_of_nonneg hthetaNonneg, one_mul]
  exact intervalIntegral.integral_mono_on hx hapInt hthetaInt fun t ht => by
    exact div_le_div_of_nonneg_right (f3ThetaAP_le_theta A a t) <|
      mul_nonneg (by linarith [ht.1]) (sq_nonneg _)

end OmegaBalance
