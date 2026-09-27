import OmegaBalance.F3BFTBConsecutiveAssembly
import Mathlib.Data.Finset.Sort

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

end OmegaBalance
