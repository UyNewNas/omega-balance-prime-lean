import OmegaBalance.F3BFTBPigeonhole
import OmegaBalance.F3ConsecutiveRuns

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

theorem bftb_consecutivePrimes_of_exact_affine_offset_interval
    {g n lo hi s t : ℕ} {S : Finset ℕ}
    (hsI : s ∈ Finset.Icc lo hi)
    (htI : t ∈ Finset.Icc lo hi)
    (hexact : ∀ u ∈ Finset.Icc lo hi,
      (g * n + u).Prime ↔ u ∈ S)
    (hsS : s ∈ S) (htS : t ∈ S)
    (hst : s < t)
    (hadj : ∀ u ∈ S, ¬ (s < u ∧ u < t)) :
    ConsecutivePrimes (g * n + s) (g * n + t) := by
  have hsp : (g * n + s).Prime := (hexact s hsI).2 hsS
  have htp : (g * n + t).Prime := (hexact t htI).2 htS
  have hlt : g * n + s < g * n + t := by omega
  refine ⟨hsp, htp, hlt, ?_⟩
  intro x hsx hxt hxp
  let u : ℕ := x - g * n
  have hux : g * n + u = x := by
    dsimp [u]
    omega
  have hsu : s < u := by
    dsimp [u]
    omega
  have hut : u < t := by
    dsimp [u]
    omega
  have hsBounds := Finset.mem_Icc.mp hsI
  have htBounds := Finset.mem_Icc.mp htI
  have huI : u ∈ Finset.Icc lo hi := by
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hup : (g * n + u).Prime := by
    rw [hux]
    exact hxp
  have huS : u ∈ S := (hexact u huI).1 hup
  exact (hadj u huS) ⟨hsu, hut⟩

end OmegaBalance
