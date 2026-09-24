import OmegaBalance.FactorSumFamily
import Mathlib.Data.List.Prime
import Mathlib.NumberTheory.LucasPrimality

namespace OmegaBalance

theorem lucasPrime_of_factorList (p a : ℕ) (factors : List ℕ)
    (hprod : factors.prod = p - 1)
    (hprime : ∀ q ∈ factors, q.Prime)
    (ha : (a : ZMod p) ^ (p - 1) = 1)
    (hd : ∀ q ∈ factors, (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p) ha
  intro q hq hqdiv
  apply hd q
  apply mem_list_primes_of_dvd_prod hq.prime
  · intro r hr
    exact (hprime r hr).prime
  · rw [hprod]
    exact hqdiv

end OmegaBalance
