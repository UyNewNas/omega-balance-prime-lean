import OmegaBalance.F3PrimeDensityAP

open Filter Finset Asymptotics
open scoped Topology Chebyshev

namespace OmegaBalance

noncomputable def f3APPrimes (A a : ℕ) (x : ℝ) : Finset ℕ :=
  (Icc 0 ⌊x⌋₊).filter fun p => p.Prime ∧ p % A = a

lemma f3ThetaAP_eq_sum_apPrimes (A a : ℕ) (x : ℝ) :
    f3ThetaAP A a x = ∑ p ∈ f3APPrimes A a x, Real.log p := by
  rw [f3ThetaAP, f3APPrimes, ← Finset.sum_filter]
  congr 1
  ext p
  simp [and_assoc]

lemma f3PrimeAPCountingReal_eq_card_apPrimes (A a : ℕ) (x : ℝ) :
    f3PrimeAPCountingReal A a x = (f3APPrimes A a x).card := by
  rfl

lemma f3ThetaAP_nonneg (A a : ℕ) (x : ℝ) : 0 ≤ f3ThetaAP A a x := by
  rw [f3ThetaAP_eq_sum_apPrimes]
  exact Finset.sum_nonneg fun p hp => Real.log_nonneg <| by
    have hprime := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hprime.one_lt.le

end OmegaBalance
