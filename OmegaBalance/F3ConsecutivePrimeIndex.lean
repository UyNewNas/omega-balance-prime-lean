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


/--
Exact prime-index form of the Banks--Freiberg--Turnage-Butterbaugh Corollary 3
shape.  The constant C is chosen before a,D,B, so it depends only on L.
This is a proposition, not an axiom or theorem assertion.
-/
def BFTBPrimeIndexRuns : Prop :=
  ∀ L : ℕ, 2 ≤ L →
    ∃ C : ℕ, ∀ a D B : ℕ,
      a.Coprime D → 3 ≤ D →
      PrimeIndexResidueRunBounded a D L B (D * C)

/-- Specialize an indexed BFTB statement to exact bounded constant-F₃ runs. -/
theorem f3PrimeIndexRunsBounded_of_BFTB
    (hBFTB : BFTBPrimeIndexRuns)
    {c : ℤ} (hc : c ≠ 0) {L : ℕ} (hL : 2 ≤ L) :
    ∃ C : ℕ, ∀ B : ℕ,
      F3PrimeIndexRunBounded c L B (f3RunModulus c * C) := by
  rcases hBFTB L hL with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro B
  apply f3PrimeIndexRunBounded_of_residue hc
  exact hC (f3RunResidue c) (f3RunModulus c) B
    (f3RunResidue_coprime hc) (f3RunModulus_ge_three c)


/-- The length-one indexed RUN case is unconditional, with span exactly zero. -/
theorem f3PrimeIndexRunBounded_one {c : ℤ} (hc : c ≠ 0) (B : ℕ) :
    F3PrimeIndexRunBounded c 1 B 0 := by
  obtain ⟨p, hp, hB⟩ :=
    Set.infinite_iff_exists_gt.mp (f3_prime_level_infinite hc) B
  have hinf : {q : ℕ | q.Prime}.Infinite := Nat.infinite_setOfPred_prime
  have hrange : p ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite hinf]
    exact hp.1
  rcases hrange with ⟨r, hr⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · simpa [hr] using hB
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [hr] using hp.2.2
  · simp

end OmegaBalance
