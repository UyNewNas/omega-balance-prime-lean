import OmegaBalance.F3BFTBConsecutiveAssembly
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn

namespace OmegaBalance

theorem bftb_orderEmbOfFin_adjacent_no_mem_between
    {S : Finset ℕ} {i j : Fin S.card}
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    ∀ u ∈ S, ¬ (
      S.orderEmbOfFin rfl i < u ∧
      u < S.orderEmbOfFin rfl j) := by
  intro u hu hbetween
  have huRange : u ∈ Set.range (S.orderEmbOfFin rfl) := by
    simpa using hu
  rcases huRange with ⟨k, hk⟩
  rw [← hk] at hbetween
  have hik : i < k :=
    (S.orderEmbOfFin rfl).lt_iff_lt.mp hbetween.1
  have hkj : k < j :=
    (S.orderEmbOfFin rfl).lt_iff_lt.mp hbetween.2
  have hik' : (i : ℕ) < (k : ℕ) := hik
  have hkj' : (k : ℕ) < (j : ℕ) := hkj
  omega

/--
Adjacent offsets in the increasing enumeration of an exact affine prime
pattern give genuinely consecutive primes in the full prime sequence.
-/
theorem bftb_consecutivePrimes_of_orderEmbOfFin_adjacent
    {g n lo hi : ℕ} {S : Finset ℕ}
    (hSI : S ⊆ Finset.Icc lo hi)
    (hexact : ∀ u ∈ Finset.Icc lo hi,
      (g * n + u).Prime ↔ u ∈ S)
    {i j : Fin S.card}
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    ConsecutivePrimes
      (g * n + S.orderEmbOfFin rfl i)
      (g * n + S.orderEmbOfFin rfl j) := by
  have hiS : S.orderEmbOfFin rfl i ∈ S :=
    S.orderEmbOfFin_mem rfl i
  have hjS : S.orderEmbOfFin rfl j ∈ S :=
    S.orderEmbOfFin_mem rfl j
  have hijlt : i < j := by
    exact hij ▸ Nat.lt_succ_self (i : ℕ)
  have hofflt :
      S.orderEmbOfFin rfl i < S.orderEmbOfFin rfl j :=
    (S.orderEmbOfFin rfl).strictMono hijlt
  exact bftb_consecutivePrimes_of_exact_affine_offset_interval
    (hSI hiS) (hSI hjS) hexact hiS hjS hofflt
    (bftb_orderEmbOfFin_adjacent_no_mem_between hij)

/-- A list whose adjacent pairs are consecutive primes and whose entries are
prime is a genuine consecutive-prime block. -/
theorem consecutivePrimeBlock_of_isChain
    {ps : List ℕ}
    (hchain : ps.IsChain ConsecutivePrimes)
    (hprime : ∀ p ∈ ps, p.Prime) :
    ConsecutivePrimeBlock ps := by
  revert hchain hprime
  induction ps with
  | nil =>
      intro _ _
      simp [ConsecutivePrimeBlock]
  | cons p ps ih =>
      intro hchain hprime
      cases ps with
      | nil =>
          simpa [ConsecutivePrimeBlock] using hprime p (by simp)
      | cons q qs =>
          have hc := List.isChain_cons_cons.mp hchain
          rw [ConsecutivePrimeBlock]
          refine ⟨hc.1, ih hc.2 ?_⟩
          intro r hr
          exact hprime r (by simp [hr])

/--
The increasing enumeration of an exact affine prime pattern is itself a
genuine consecutive-prime block in the full prime sequence.
-/
theorem bftb_consecutivePrimeBlock_of_orderEmbOfFin
    {g n lo hi : ℕ} {S : Finset ℕ}
    (hSI : S ⊆ Finset.Icc lo hi)
    (hexact : ∀ u ∈ Finset.Icc lo hi,
      (g * n + u).Prime ↔ u ∈ S) :
    ConsecutivePrimeBlock
      (List.ofFn fun i : Fin S.card =>
        g * n + S.orderEmbOfFin rfl i) := by
  apply consecutivePrimeBlock_of_isChain
  · rw [List.isChain_iff_getElem]
    intro i hiIndex
    have hiCard : i + 1 < S.card := by
      simpa using hiIndex
    have hi0 : i < S.card := by omega
    have hcon :=
      bftb_consecutivePrimes_of_orderEmbOfFin_adjacent
        hSI hexact
        (i := ⟨i, hi0⟩)
        (j := ⟨i + 1, hiCard⟩)
        rfl
    simpa using hcon
  · rw [List.forall_mem_ofFn_iff]
    intro i
    have hiS : S.orderEmbOfFin rfl i ∈ S :=
      S.orderEmbOfFin_mem rfl i
    exact (hexact _ (hSI hiS)).2 hiS

end OmegaBalance
