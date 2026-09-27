import OmegaBalance.F3ConsecutiveRuns
import Mathlib.NumberTheory.PrimeCounting

namespace OmegaBalance

theorem consecutivePrimes_nth_prime (r : ℕ) :
    ConsecutivePrimes (Nat.nth Nat.Prime r) (Nat.nth Nat.Prime (r + 1)) := by
  have hinf : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOfPred_prime
  have hp : (Nat.nth Nat.Prime r).Prime := Nat.prime_nth_prime r
  have hq : (Nat.nth Nat.Prime (r + 1)).Prime := Nat.prime_nth_prime (r + 1)
  have hlt : Nat.nth Nat.Prime r < Nat.nth Nat.Prime (r + 1) :=
    (Nat.nth_lt_nth hinf).2 (by omega)
  refine ⟨hp, hq, hlt, ?_⟩
  intro x hx1 hx2 hxprime
  have hxrange : x ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite hinf]
    exact hxprime
  rcases hxrange with ⟨j, rfl⟩
  have hj1 : r < j := (Nat.nth_lt_nth hinf).1 hx1
  have hj2 : j < r + 1 := (Nat.nth_lt_nth hinf).1 hx2
  omega

def PrimeIndexResidueRunBounded (a D L B H : ℕ) : Prop :=
  ∃ r : ℕ,
    B < Nat.nth Nat.Prime r ∧
    (∀ i : ℕ, i < L →
      Nat.nth Nat.Prime (r + i) ≡ a [MOD D]) ∧
    Nat.nth Nat.Prime (r + (L - 1)) - Nat.nth Nat.Prime r ≤ H

def F3PrimeIndexRunBounded (c : ℤ) (L B H : ℕ) : Prop :=
  ∃ r : ℕ,
    B < Nat.nth Nat.Prime r ∧
    (∀ i : ℕ, i < L →
      f3 (Nat.nth Nat.Prime (r + i)) = c) ∧
    Nat.nth Nat.Prime (r + (L - 1)) - Nat.nth Nat.Prime r ≤ H

theorem f3PrimeIndexRunBounded_of_residue
    {c : ℤ} (hc : c ≠ 0) {L B H : ℕ}
    (h : PrimeIndexResidueRunBounded
      (f3RunResidue c) (f3RunModulus c) L B H) :
    F3PrimeIndexRunBounded c L B H := by
  rcases h with ⟨r, hB, hmod, hspan⟩
  refine ⟨r, hB, ?_, hspan⟩
  intro i hi
  have hp : (Nat.nth Nat.Prime (r + i)).Prime := Nat.prime_nth_prime (r + i)
  have hp1 : 1 < Nat.nth Nat.Prime (r + i) :=
    lt_of_lt_of_le (by decide : 1 < 2) hp.two_le
  exact f3_of_modEq_runResidue hp1 hc (hmod i hi)

end OmegaBalance
