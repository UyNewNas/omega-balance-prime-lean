import OmegaBalance.F3BFTBCRT

namespace OmegaBalance

theorem bftbAuxPrime_prime (r t : ℕ) :
    (Nat.nth Nat.Prime (r + t)).Prime := by
  exact Nat.prime_nth_prime (r + t)

theorem bftbAuxPrime_lower_bound (r t : ℕ) :
    Nat.nth Nat.Prime r ≤ Nat.nth Nat.Prime (r + t) := by
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega)

theorem bftbAuxPrime_injective (r : ℕ) :
    Function.Injective (fun t => Nat.nth Nat.Prime (r + t)) := by
  intro s t hst
  have hidx : r + s = r + t :=
    Nat.nth_injective Nat.infinite_setOfPred_prime hst
  omega

theorem bftbAuxPrime_pairwise_coprime (r : ℕ) (T : Finset ℕ) :
    Set.Pairwise (↑T : Set ℕ)
      (fun s t =>
        (Nat.nth Nat.Prime (r + s)).Coprime
          (Nat.nth Nat.Prime (r + t))) := by
  intro s hs t ht hst
  apply (Nat.coprime_primes (bftbAuxPrime_prime r s) (bftbAuxPrime_prime r t)).mpr
  intro heq
  exact hst ((bftbAuxPrime_injective r) heq)

theorem exists_bftbAuxPrime_family_gt (B : ℕ) :
    ∃ r : ℕ, ∀ t : ℕ, B < Nat.nth Nat.Prime (r + t) := by
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
    {r t g : ℕ} (hg : 0 < g)
    (hlt : g < Nat.nth Nat.Prime (r + t)) :
    g.Coprime (Nat.nth Nat.Prime (r + t)) := by
  rw [Nat.coprime_comm]
  apply (bftbAuxPrime_prime r t).coprime_iff_not_dvd.mpr
  intro hdvd
  have hle : Nat.nth Nat.Prime (r + t) ≤ g := Nat.le_of_dvd hg hdvd
  exact (not_lt_of_ge hle) hlt

end OmegaBalance
