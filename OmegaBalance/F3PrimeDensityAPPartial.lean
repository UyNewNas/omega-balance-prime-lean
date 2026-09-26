import OmegaBalance.F3PrimeDensityAPBound

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma f3IntegrableOn_thetaAP_div_id_mul_log_sq (A a : ℕ) (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t => f3ThetaAP A a t / (t * Real.log t ^ 2))
      (Set.Icc 2 x) MeasureTheory.volume := by
  conv => arg 1; ext t
          rw [f3ThetaAP, div_eq_mul_one_div, mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have htlog : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 <| by
    simp
    grind
  fun_prop (disch := assumption)

end OmegaBalance
