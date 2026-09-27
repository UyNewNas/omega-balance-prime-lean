import OmegaBalance.F3PrimeDensityAPBasic

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

lemma f3ThetaAP_le_count_mul_log (A a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    f3ThetaAP A a x ≤ f3PrimeAPCountingReal A a x * Real.log x := by
  rw [f3ThetaAP_eq_sum_apPrimes, f3PrimeAPCountingReal_eq_card_apPrimes]
  calc
    ∑ p ∈ f3APPrimes A a x, Real.log p
        ≤ ∑ _p ∈ f3APPrimes A a x, Real.log x := by
          apply Finset.sum_le_sum
          intro p hp
          apply Real.strictMonoOn_log.monotoneOn
          · have hprime := (Finset.mem_filter.mp hp).2.1
            exact (show (0 : ℝ) < p by exact_mod_cast hprime.pos)
          · exact (show (0 : ℝ) < x by linarith)
          · exact (Nat.cast_le.mpr (Finset.mem_Icc.mp
              (Finset.mem_filter.mp hp).1).2).trans (Nat.floor_le (by linarith))
    _ = (f3APPrimes A a x).card * Real.log x := by simp

end OmegaBalance
