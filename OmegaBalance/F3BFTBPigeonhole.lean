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

/--
Combine the many-primes pigeonhole step with maximality and the finite ambient
tuple to obtain one threshold beyond which every offset outside the chosen
maximal subtuple is composite.
-/
theorem bftb_exists_large_maximal_with_uniform_exclusion
    (value : ℕ → ℕ → ℕ) (H : Finset ℕ) {m : ℕ}
    (hmany : (BFTBAtLeastPrimeCountSet value H m).Infinite) :
    ∃ S : Finset ℕ, ∃ B : ℕ,
      S ⊆ H ∧
      m ≤ S.card ∧
      (BFTBSimultaneousPrimeSet value S).Infinite ∧
      ∀ n : ℕ, B < n →
        n ∈ BFTBSimultaneousPrimeSet value S →
        ∀ h : ℕ, h ∈ H → h ∉ S → ¬ (value n h).Prime := by
  obtain ⟨S, hSH, hcard, hSinf, hmax⟩ :=
    bftb_exists_large_maximal_simultaneous_subset value H hmany
  obtain ⟨B, hB⟩ :=
    bftb_maximal_extras_uniformly_eventually_composite hSH hmax
  exact ⟨S, B, hSH, hcard, hSinf, hB⟩

/-- Translation parameters whose prime offsets inside H are exactly S. -/
def BFTBExactPrimePatternSet
    (value : ℕ → ℕ → ℕ) (H S : Finset ℕ) : Set ℕ :=
  {n : ℕ | ∀ h ∈ H, (value n h).Prime ↔ h ∈ S}

/--
A maximal infinitely simultaneous-prime subtuple occurs as the exact prime
pattern inside the ambient finite tuple for infinitely many parameters.
-/
theorem bftb_exact_prime_pattern_infinite_of_maximal
    {value : ℕ → ℕ → ℕ} {H S : Finset ℕ}
    (hSH : S ⊆ H)
    (hSinf : (BFTBSimultaneousPrimeSet value S).Infinite)
    (hmax : ∀ T : Finset ℕ, T ⊆ H →
      (BFTBSimultaneousPrimeSet value T).Infinite →
      T.card ≤ S.card) :
    (BFTBExactPrimePatternSet value H S).Infinite := by
  obtain ⟨B, hB⟩ :=
    bftb_maximal_extras_uniformly_eventually_composite hSH hmax
  have htail :
      (BFTBSimultaneousPrimeSet value S \ Set.Iic B).Infinite :=
    hSinf.sdiff (Set.finite_Iic B)
  apply htail.mono
  intro n hn
  rcases hn with ⟨hnS, hnB⟩
  have hBn : B < n := by
    simpa only [Set.mem_Iic, not_le] using hnB
  change ∀ h ∈ H, (value n h).Prime ↔ h ∈ S
  intro h hhH
  constructor
  · intro hp
    by_contra hhS
    exact (hB n hBn hnS h hhH hhS) hp
  · intro hhS
    exact hnS h hhS

/--
If infinitely many parameters make at least m offsets prime, then there is a
fixed subtuple of cardinality at least m which is exactly the set of prime
offsets inside H for infinitely many parameters.
-/
theorem bftb_exists_large_exact_prime_pattern
    (value : ℕ → ℕ → ℕ) (H : Finset ℕ) {m : ℕ}
    (hmany : (BFTBAtLeastPrimeCountSet value H m).Infinite) :
    ∃ S : Finset ℕ,
      S ⊆ H ∧
      m ≤ S.card ∧
      (BFTBExactPrimePatternSet value H S).Infinite := by
  obtain ⟨S, hSH, hcard, hSinf, hmax⟩ :=
    bftb_exists_large_maximal_simultaneous_subset value H hmany
  exact ⟨S, hSH, hcard,
    bftb_exact_prime_pattern_infinite_of_maximal hSH hSinf hmax⟩

end OmegaBalance
