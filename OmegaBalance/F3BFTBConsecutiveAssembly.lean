import OmegaBalance.F3BFTBPigeonhole

namespace OmegaBalance

theorem bftb_exact_prime_pattern_extend
    {value : ℕ → ℕ → ℕ} {I H S : Finset ℕ} {n : ℕ}
    (hSH : S ⊆ H)
    (hn : n ∈ BFTBExactPrimePatternSet value H S)
    (hout : ∀ t ∈ I, t ∉ H → ¬ (value n t).Prime) :
    ∀ t ∈ I, (value n t).Prime ↔ t ∈ S := by
  intro t htI
  by_cases htH : t ∈ H
  · exact hn t htH
  · constructor
    · intro hp
      exact False.elim (hout t htI htH hp)
    · intro htS
      exact False.elim (htH (hSH htS))

end OmegaBalance
