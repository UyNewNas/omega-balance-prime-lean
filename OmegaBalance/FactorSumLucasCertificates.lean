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


theorem prime_672626441909 : Nat.Prime 672626441909 := by
  apply lucasPrime_of_factorList 672626441909 2 [2, 2, 269939, 622943]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num

theorem prime_672625902031 : Nat.Prime 672625902031 := by
  apply lucasPrime_of_factorList 672625902031 6 [2, 3, 5, 83059, 269939]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_916065462437 : Nat.Prime 916065462437 := by
  apply lucasPrime_of_factorList 916065462437 2 [2, 2, 211, 1493, 726983]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_916064832391 : Nat.Prime 916064832391 := by
  apply lucasPrime_of_factorList 916064832391 6 [2, 3, 5, 211, 1493, 96931]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num


theorem prime_1676030389155588931 : Nat.Prime 1676030389155588931 := by
  apply lucasPrime_of_factorList 1676030389155588931 2
    [2, 3, 5, 83059, 672626441909]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_672626441909
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_2663854240184425411 : Nat.Prime 2663854240184425411 := by
  apply lucasPrime_of_factorList 2663854240184425411 3
    [2, 3, 5, 96931, 916065462437]
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact prime_916065462437
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num

end OmegaBalance
