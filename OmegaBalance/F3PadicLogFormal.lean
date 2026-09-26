import OmegaBalance.F3PadicLog
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Formal power-series bridge prototypes for the 3-adic F₃ logarithm

These kernel-checked examples validate the pinned-mathlib interfaces needed
for the remaining logarithmic homomorphism layer. They intentionally add no
public theorem before the proof scripts have passed the repository gates.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

example {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    f3PadicLogOnePlus x =
      PowerSeries.eval₂ (RingHom.id ℚ_[3]) x (PowerSeries.log ℚ_[3]) := by
  have heval : PowerSeries.HasEval x :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
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

example {x : ℚ_[3]} (hx : PowerSeries.HasEval x) :
    NormedSpace.exp x =
      PowerSeries.eval₂ (RingHom.id ℚ_[3]) x (PowerSeries.exp ℚ_[3]) := by
  rw [NormedSpace.exp_eq_tsum ℚ]
  rw [PowerSeries.eval₂_eq_tsum RingHom.continuous_id hx]
  apply tsum_congr
  intro k
  simp [PowerSeries.coeff_exp, Algebra.smul_def, div_eq_mul_inv]

end OmegaBalance
