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


/--
Complete finite auxiliary-prime + CRT package used at the start of BFTB Theorem 1.
A single bound `B` dominating `g` and all offsets lets us choose successive primes
above `B`; they are pairwise coprime, coprime to `g`, and too large for distinct
protected/excluded offsets to collide modulo them.
-/
theorem bftb_exists_crt_shift_from_bound
    {T H : Finset ℕ} {g B : ℕ}
    (hg : 0 < g) (hgB : g ≤ B)
    (hT : ∀ t ∈ T, t ≤ B)
    (hH : ∀ h ∈ H, h ≤ B)
    (hdisj : Disjoint T H) :
    ∃ r A : ℕ,
      (∀ t ∈ T, Nat.nth Nat.Prime (r + t) ∣ g * A + t) ∧
      (∀ t ∈ T, ∀ h ∈ H,
        ¬ Nat.nth Nat.Prime (r + t) ∣ g * A + h) := by
  obtain ⟨r, hr⟩ := exists_bftbAuxPrime_family_gt B
  have hqprime : ∀ t ∈ T, (Nat.nth Nat.Prime (r + t)).Prime := by
    intro t ht
    exact bftbAuxPrime_prime r t
  have hpair :
      Set.Pairwise (↑T : Set ℕ)
        (fun s t =>
          (Nat.nth Nat.Prime (r + s)).Coprime
            (Nat.nth Nat.Prime (r + t))) :=
    bftbAuxPrime_pairwise_coprime r T
  have hgq : ∀ t ∈ T, g.Coprime (Nat.nth Nat.Prime (r + t)) := by
    intro t ht
    exact bftbAuxPrime_coprime_of_lt hg (lt_of_le_of_lt hgB (hr t))
  have htlt : ∀ t ∈ T, t < Nat.nth Nat.Prime (r + t) := by
    intro t ht
    exact lt_of_le_of_lt (hT t ht) (hr t)
  have hhlt :
      ∀ t ∈ T, ∀ h ∈ H, h < Nat.nth Nat.Prime (r + t) := by
    intro t ht h hh
    exact lt_of_le_of_lt (hH h hh) (hr t)
  obtain ⟨A, hA1, hA2⟩ :=
    bftb_exists_crt_shift_of_large_moduli
      (fun t => Nat.nth Nat.Prime (r + t))
      hqprime hpair hgq hdisj htlt hhlt
  exact ⟨r, A, hA1, hA2⟩

end OmegaBalance
