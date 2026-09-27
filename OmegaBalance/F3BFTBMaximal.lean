import OmegaBalance.F3BFTBCRTComposite
import Mathlib.Data.Set.Finite.Lattice

namespace OmegaBalance

/-- Translation parameters for which every offset in a finite tuple is prime. -/
def BFTBSimultaneousPrimeSet (value : ℕ → ℕ → ℕ) (S : Finset ℕ) : Set ℕ :=
  {n : ℕ | ∀ h ∈ S, (value n h).Prime}

theorem bftbSimultaneousPrimeSet_insert
    (value : ℕ → ℕ → ℕ) (S : Finset ℕ) (h : ℕ) :
    BFTBSimultaneousPrimeSet value (insert h S) =
      {n : ℕ | n ∈ BFTBSimultaneousPrimeSet value S ∧ (value n h).Prime} := by
  ext n
  simp [BFTBSimultaneousPrimeSet, and_left_comm, and_comm, and_assoc]

/--
If S is a subset of H and has maximal cardinality among subsets of H that are
simultaneously prime for infinitely many translation parameters, then adjoining
any new element of H outside S can occur only for finitely many parameters.

This is the finitary maximal-subset step used in BFTB Theorem 1.
-/
theorem bftb_maximal_extra_finite
    {value : ℕ → ℕ → ℕ} {H S : Finset ℕ}
    (hSH : S ⊆ H)
    (hmax : ∀ T : Finset ℕ, T ⊆ H →
      (BFTBSimultaneousPrimeSet value T).Infinite →
      T.card ≤ S.card)
    {h : ℕ} (hhH : h ∈ H) (hhS : h ∉ S) :
    ({n : ℕ |
      n ∈ BFTBSimultaneousPrimeSet value S ∧ (value n h).Prime} : Set ℕ).Finite := by
  by_contra hfinite
  have hinf : (BFTBSimultaneousPrimeSet value (insert h S)).Infinite := by
    rw [bftbSimultaneousPrimeSet_insert]
    exact hfinite
  have hsub : insert h S ⊆ H := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact hhH
    · exact hSH hxS
  have hcard := hmax (insert h S) hsub hinf
  rw [Finset.card_insert_of_notMem hhS] at hcard
  omega

/--
For each tuple offset outside a maximal simultaneous-prime subset, there is a
threshold after which that offset is composite whenever all offsets in the
maximal subset are prime.
-/
theorem bftb_maximal_extra_eventually_composite
    {value : ℕ → ℕ → ℕ} {H S : Finset ℕ}
    (hSH : S ⊆ H)
    (hmax : ∀ T : Finset ℕ, T ⊆ H →
      (BFTBSimultaneousPrimeSet value T).Infinite →
      T.card ≤ S.card) :
    ∀ h ∈ H, h ∉ S, ∃ B : ℕ, ∀ n : ℕ, B < n →
      n ∈ BFTBSimultaneousPrimeSet value S →
      ¬ (value n h).Prime := by
  intro h hhH hhS
  have hfinite :=
    bftb_maximal_extra_finite hSH hmax hhH hhS
  rcases hfinite.bddAbove with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n hBn hnS hnprime
  have hmem :
      n ∈ ({n : ℕ |
        n ∈ BFTBSimultaneousPrimeSet value S ∧ (value n h).Prime} : Set ℕ) :=
    ⟨hnS, hnprime⟩
  have hnle : n ≤ B := hB hmem
  omega

end OmegaBalance
