import OmegaBalance.F3BFTBMaximal
import Mathlib.Data.Finset.Powerset

namespace OmegaBalance

def BFTBAtLeastPrimeCountSet
    (value : ℕ → ℕ → ℕ) (H : Finset ℕ) (m : ℕ) : Set ℕ :=
  {n : ℕ | m ≤ (H.filter fun h => (value n h).Prime).card}

theorem bftb_exists_infinite_simultaneous_subset_of_many_primes
    {value : ℕ → ℕ → ℕ} {H : Finset ℕ} {m : ℕ}
    (hmany : (BFTBAtLeastPrimeCountSet value H m).Infinite) :
    ∃ S : Finset ℕ,
      S ⊆ H ∧
      S.card = m ∧
      (BFTBSimultaneousPrimeSet value S).Infinite := by
  classical
  have hex :
      ∃ S ∈ H.powersetCard m,
        (BFTBSimultaneousPrimeSet value S).Infinite := by
    by_contra hno
    have hfinite_each :
        ∀ S ∈ H.powersetCard m,
          (BFTBSimultaneousPrimeSet value S).Finite := by
      intro S hS
      exact Set.not_infinite.mp (by
        intro hInf
        exact hno ⟨S, hS, hInf⟩)
    have hunion_finite :
        (⋃ S ∈ (H.powersetCard m : Set (Finset ℕ)),
          BFTBSimultaneousPrimeSet value S).Finite := by
      apply (H.powersetCard m).finite_toSet.biUnion
      intro S hS
      exact hfinite_each S hS
    have hsubset :
        BFTBAtLeastPrimeCountSet value H m ⊆
          ⋃ S ∈ (H.powersetCard m : Set (Finset ℕ)),
            BFTBSimultaneousPrimeSet value S := by
      intro n hn
      let P : Finset ℕ := H.filter fun h => (value n h).Prime
      have hcard : m ≤ P.card := by
        simpa [BFTBAtLeastPrimeCountSet, P] using hn
      obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hcard
      have hSH : S ⊆ H := hSP.trans (Finset.filter_subset _ _)
      have hSC : S ∈ H.powersetCard m :=
        Finset.mem_powersetCard.mpr ⟨hSH, hScard⟩
      have hnS : n ∈ BFTBSimultaneousPrimeSet value S := by
        intro h hhS
        exact (Finset.mem_filter.mp (hSP hhS)).2
      exact Set.mem_biUnion hSC hnS
    exact hmany.not_finite (hunion_finite.subset hsubset)
  obtain ⟨S, hSC, hInf⟩ := hex
  have hS := Finset.mem_powersetCard.mp hSC
  exact ⟨S, hS.1, hS.2, hInf⟩

theorem bftb_maximal_card_ge_of_many_primes
    {value : ℕ → ℕ → ℕ} {H S : Finset ℕ} {m : ℕ}
    (hSH : S ⊆ H)
    (hmax : ∀ T : Finset ℕ, T ⊆ H →
      (BFTBSimultaneousPrimeSet value T).Infinite →
      T.card ≤ S.card)
    (hmany : (BFTBAtLeastPrimeCountSet value H m).Infinite) :
    m ≤ S.card := by
  obtain ⟨T, hTH, hTcard, hTinf⟩ :=
    bftb_exists_infinite_simultaneous_subset_of_many_primes hmany
  have hle := hmax T hTH hTinf
  simpa [hTcard] using hle

theorem bftb_exists_large_maximal_simultaneous_subset
    (value : ℕ → ℕ → ℕ) (H : Finset ℕ) {m : ℕ}
    (hmany : (BFTBAtLeastPrimeCountSet value H m).Infinite) :
    ∃ S : Finset ℕ,
      S ⊆ H ∧
      m ≤ S.card ∧
      (BFTBSimultaneousPrimeSet value S).Infinite ∧
      ∀ T : Finset ℕ, T ⊆ H →
        (BFTBSimultaneousPrimeSet value T).Infinite →
        T.card ≤ S.card := by
  obtain ⟨S, hSH, hSinf, hmax⟩ :=
    bftb_exists_maximal_simultaneous_subset value H
  have hcard :=
    bftb_maximal_card_ge_of_many_primes hSH hmax hmany
  exact ⟨S, hSH, hcard, hSinf, hmax⟩

end OmegaBalance
