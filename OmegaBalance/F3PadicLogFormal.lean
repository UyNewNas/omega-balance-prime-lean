import OmegaBalance.F3PadicLogIsometry
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Formal-power-series bridge for the genuine 3-adic F₃ logarithm

This file connects the explicitly summed logarithm used by the project with
mathlib's formal `PowerSeries.log`.  The bridge is evaluated over `ℚ_[3]`
itself, so no continuity claim for the map from the usual topology on `ℚ`
to the 3-adics is needed.

It also records the analogous bridge for the exponential series.  These are
the formal/analytic interfaces needed for the remaining homomorphism identity
`L(mn)=L(m)+L(n)`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Every point of the open 3-adic unit ball is a legitimate evaluation point
for a formal power series. -/
theorem f3Padic_hasEval_of_norm_lt_one {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    PowerSeries.HasEval x :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- The explicitly summed project logarithm is exactly the evaluation of
mathlib's formal logarithm over `ℚ_[3]`. -/
theorem f3PadicLogOnePlus_eq_powerSeries_eval {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    f3PadicLogOnePlus x =
      PowerSeries.eval₂ (RingHom.id ℚ_[3]) x (PowerSeries.log ℚ_[3]) := by
  have heval : PowerSeries.HasEval x := f3Padic_hasEval_of_norm_lt_one hx
  have hsum :
      Summable (fun d : ℕ =>
        (RingHom.id ℚ_[3]) (PowerSeries.coeff d (PowerSeries.log ℚ_[3])) * x ^ d) :=
    (PowerSeries.hasSum_eval₂ RingHom.continuous_id heval
      (PowerSeries.log ℚ_[3])).summable
  rw [PowerSeries.eval₂_eq_tsum RingHom.continuous_id heval]
  unfold f3PadicLogOnePlus
  rw [hsum.tsum_eq_zero_add]
  simp only [PowerSeries.coeff_log, if_pos, map_zero, zero_mul, zero_add]
  rw [(summable_f3PadicLogTerm hx).tsum_eq]
  apply tsum_congr
  intro k
  simp [f3PadicLogTerm, PowerSeries.coeff_log, pow_add, div_eq_mul_inv,
    Algebra.smul_def]

/-- For every admissible integer input, `L(n)` is evaluation of the genuine
formal logarithm at `U(n)-1`. -/
theorem f3PadicLog_eq_powerSeries_eval {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3PadicLog n =
      PowerSeries.eval₂ (RingHom.id ℚ_[3]) (f3PadicDelta n)
        (PowerSeries.log ℚ_[3]) := by
  unfold f3PadicLog
  exact f3PadicLogOnePlus_eq_powerSeries_eval (f3PadicDelta_norm_lt_one hn h3)

/-- The already constructed F₃ logarithm is itself topologically nilpotent on
the admissible domain. -/
theorem f3PadicLog_hasEval {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    PowerSeries.HasEval (f3PadicLog n) := by
  apply f3Padic_hasEval_of_norm_lt_one
  rw [f3PadicLog_norm_eq_delta_norm hn h3]
  exact f3PadicDelta_norm_lt_one hn h3

/-- mathlib's analytic exponential on `ℚ_[3]` agrees, at every
topologically nilpotent point, with evaluation of the formal exponential
series over `ℚ_[3]`. -/
theorem f3PadicExp_eq_powerSeries_eval {x : ℚ_[3]} (hx : PowerSeries.HasEval x) :
    NormedSpace.exp x =
      PowerSeries.eval₂ (RingHom.id ℚ_[3]) x (PowerSeries.exp ℚ_[3]) := by
  rw [NormedSpace.exp_eq_tsum ℚ]
  rw [PowerSeries.eval₂_eq_tsum RingHom.continuous_id hx]
  apply tsum_congr
  intro k
  simp [PowerSeries.coeff_exp, Algebra.smul_def, div_eq_mul_inv]

end OmegaBalance
