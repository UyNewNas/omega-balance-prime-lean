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

end OmegaBalance
