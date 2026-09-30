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


/-- The BFTB constant can be chosen uniformly in the nonzero target F₃ level. -/
theorem f3PrimeIndexRunsBounded_uniform_of_BFTB
    (hBFTB : BFTBPrimeIndexRuns)
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ C : ℕ, ∀ c : ℤ, c ≠ 0 → ∀ B : ℕ,
      F3PrimeIndexRunBounded c L B (f3RunModulus c * C) := by
  rcases hBFTB L hL with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro c hc B
  apply f3PrimeIndexRunBounded_of_residue hc
  exact hC (f3RunResidue c) (f3RunModulus c) B
    (f3RunResidue_coprime hc) (f3RunModulus_ge_three c)

/-- Conditional bounded RUN theorem for every positive length, including L=1. -/
theorem f3PrimeIndexRunsBounded_all_lengths_of_BFTB
    (hBFTB : BFTBPrimeIndexRuns)
    {L : ℕ} (hL : 1 ≤ L) :
    ∃ C : ℕ, ∀ c : ℤ, c ≠ 0 → ∀ B : ℕ,
      F3PrimeIndexRunBounded c L B (f3RunModulus c * C) := by
  by_cases hLone : L = 1
  · subst L
    refine ⟨0, ?_⟩
    intro c hc B
    simpa using f3PrimeIndexRunBounded_one hc B
  · have hLtwo : 2 ≤ L := by omega
    exact f3PrimeIndexRunsBounded_uniform_of_BFTB hBFTB hLtwo


/-- A start index for a bounded constant-F₃ run in the full prime enumeration. -/
def F3PrimeIndexRunAt (c : ℤ) (L H r : ℕ) : Prop :=
  (∀ i : ℕ, i < L → f3 (Nat.nth Nat.Prime (r + i)) = c) ∧
  Nat.nth Nat.Prime (r + (L - 1)) - Nat.nth Nat.Prime r ≤ H

/-- Arbitrarily far bounded indexed runs give infinitely many distinct start indices. -/
theorem f3PrimeIndexRunStarts_infinite_of_arbitrarily_far
    {c : ℤ} {L H : ℕ}
    (h : ∀ B : ℕ, F3PrimeIndexRunBounded c L B H) :
    Set.Infinite {r : ℕ | F3PrimeIndexRunAt c L H r} := by
  apply Set.infinite_iff_exists_gt.mpr
  intro M
  rcases h (Nat.nth Nat.Prime M) with ⟨r, hrgt, hrvals, hrspan⟩
  refine ⟨r, ?_, ?_⟩
  · exact ⟨hrvals, hrspan⟩
  · exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).1 hrgt

/-- Under BFTB, one C depending only on L works for every nonzero F₃ level. -/
theorem f3PrimeIndexRunStarts_infinite_uniform_of_BFTB
    (hBFTB : BFTBPrimeIndexRuns)
    {L : ℕ} (hL : 2 ≤ L) :
    ∃ C : ℕ, ∀ c : ℤ, c ≠ 0 →
      Set.Infinite {r : ℕ |
        F3PrimeIndexRunAt c L (f3RunModulus c * C) r} := by
  rcases f3PrimeIndexRunsBounded_uniform_of_BFTB hBFTB hL with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro c hc
  apply f3PrimeIndexRunStarts_infinite_of_arbitrarily_far
  exact hC c hc

/-- Literal infinitude for every positive run length, conditional only for L≥2. -/
theorem f3PrimeIndexRunStarts_infinite_all_lengths_of_BFTB
    (hBFTB : BFTBPrimeIndexRuns)
    {L : ℕ} (hL : 1 ≤ L) :
    ∃ C : ℕ, ∀ c : ℤ, c ≠ 0 →
      Set.Infinite {r : ℕ |
        F3PrimeIndexRunAt c L (f3RunModulus c * C) r} := by
  rcases f3PrimeIndexRunsBounded_all_lengths_of_BFTB hBFTB hL with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro c hc
  apply f3PrimeIndexRunStarts_infinite_of_arbitrarily_far
  exact hC c hc


/-- Every affine BFTB value D*n + (D*t+a) lies in the class a mod D. -/
theorem bftbAffineResidue_modEq (a D n t : ℕ) :
    D * n + (D * t + a) ≡ a [MOD D] := by
  have hn : D * n ≡ 0 [MOD D] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨n, rfl⟩
  have ht : D * t ≡ 0 [MOD D] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨t, rfl⟩
  have ha : a ≡ a [MOD D] := Nat.ModEq.refl a
  simpa using hn.add (ht.add ha)

/-- The affine offsets used in BFTB Corollary 3 stay coprime to D. -/
theorem bftbAffineResidue_coprime {a D : ℕ} (ha : a.Coprime D) (t : ℕ) :
    (D * t + a).Coprime D := by
  have h : D.Coprime (a + D * t) :=
    (Nat.coprime_add_mul_left_right D a t).2 ha.symm
  simpa [Nat.add_comm] using h.symm

/-- Affine scaling multiplies the endpoint span by exactly D. -/
theorem bftbAffine_span {D a n s t : ℕ} (hst : s ≤ t) :
    (D * n + (D * t + a)) - (D * n + (D * s + a)) =
      D * (t - s) := by
  have hmul : D * s ≤ D * t := Nat.mul_le_mul_left D hst
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Consequently any base span bound C becomes the exact BFTB bound D*C. -/
theorem bftbAffine_span_le {D a n s t C : ℕ}
    (hst : s ≤ t) (hC : t - s ≤ C) :
    (D * n + (D * t + a)) - (D * n + (D * s + a)) ≤ D * C := by
  rw [bftbAffine_span hst]
  exact Nat.mul_le_mul_left D hC

end OmegaBalance
