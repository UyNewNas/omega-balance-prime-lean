import OmegaBalance.F3BFTBCRT

namespace OmegaBalance

/-- The auxiliary prime assigned to offset `t`, starting from prime index `r`. -/
def bftbAuxPrime (r t : ℕ) : ℕ :=
  Nat.nth Nat.Prime (r + t)

theorem bftbAuxPrime_prime (r t : ℕ) :
    (bftbAuxPrime r t).Prime := by
  simpa [bftbAuxPrime] using Nat.prime_nth_prime (r + t)

theorem bftbAuxPrime_lower_bound (r t : ℕ) :
    Nat.nth Nat.Prime r ≤ bftbAuxPrime r t := by
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)

theorem bftbAuxPrime_injective (r : ℕ) :
    Function.Injective (bftbAuxPrime r) := by
  intro s t hst
  have hidx : r + s = r + t :=
    Nat.nth_injective Nat.infinite_setOfPred_prime (by
      simpa [bftbAuxPrime] using hst)
  omega

theorem bftbAuxPrime_pairwise_coprime (r : ℕ) (T : Finset ℕ) :
    Set.Pairwise (↑T : Set ℕ)
      (fun s t => (bftbAuxPrime r s).Coprime (bftbAuxPrime r t)) := by
  intro s hs t ht hst
  apply (Nat.coprime_primes (bftbAuxPrime_prime r s) (bftbAuxPrime_prime r t)).mpr
  intro heq
  exact hst ((bftbAuxPrime_injective r) heq)

theorem exists_bftbAuxPrime_family_gt (B : ℕ) :
    ∃ r : ℕ, ∀ t : ℕ, B < bftbAuxPrime r t := by
  obtain ⟨p, hp, hB⟩ :=
    Set.infinite_iff_exists_gt.mp Nat.infinite_setOfPred_prime B
  have hrange : p ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOfPred_prime]
    exact hp
  rcases hrange with ⟨r, rfl⟩
  refine ⟨r, ?_⟩
  intro t
  exact lt_of_lt_of_le hB (bftbAuxPrime_lower_bound r t)

theorem bftbAuxPrime_coprime_of_lt
    {r t g : ℕ} (hg : 0 < g) (hlt : g < bftbAuxPrime r t) :
    g.Coprime (bftbAuxPrime r t) := by
  rw [Nat.coprime_comm]
  apply (bftbAuxPrime_prime r t).coprime_iff_not_dvd.mpr
  intro hdvd
  have hle : bftbAuxPrime r t ≤ g := Nat.le_of_dvd hg hdvd
  exact (not_lt_of_ge hle) hlt

end OmegaBalance
