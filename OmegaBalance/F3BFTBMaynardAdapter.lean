import OmegaBalance.F3ConsecutivePrimeIndex
import Util.MaynardTao.BFT.Result

namespace OmegaBalance

/--
Adapter from the proved upstream BFTB result to the local prime-index RUN
interface. The upstream theorem gives a genuine consecutive block in the full
prime enumeration, an arbitrarily late start index, one fixed reduced residue
class, and span at most `D * C`.
-/
theorem bftbPrimeIndexRuns_unconditional : BFTBPrimeIndexRuns := by
  intro L hL
  obtain ⟨C, _hC, hsrc⟩ := MaynardBFT.consecutive_primes L (by omega)
  refine ⟨C, ?_⟩
  intro a D B ha hD
  have hDpos : 0 < D := by omega
  have hgcd : Int.gcd (a : ℤ) (D : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ha.gcd_eq_one
  obtain ⟨r, hr, hmod, hspan⟩ := hsrc D hDpos (a : ℤ) hgcd B
  refine ⟨r, ?_, ?_, ?_⟩
  · have hnth : r + 2 ≤ Nat.nth Nat.Prime r := Nat.add_two_le_nth_prime r
    omega
  · intro i hi
    exact Int.natCast_modEq_iff.mp (hmod i hi)
  · have hreindex : r + L - 1 = r + (L - 1) := by omega
    simpa [hreindex] using hspan

/--
Unconditional bounded constant-F₃ runs in the full prime enumeration. For a
fixed requested length, the BFTB constant is uniform in every nonzero F₃ level.
-/
theorem f3PrimeIndexRunStarts_infinite_unconditional
    {L : ℕ} (hL : 1 ≤ L) :
    ∃ C : ℕ, ∀ c : ℤ, c ≠ 0 →
      Set.Infinite {r : ℕ |
        F3PrimeIndexRunAt c L (f3RunModulus c * C) r} :=
  f3PrimeIndexRunStarts_infinite_all_lengths_of_BFTB
    bftbPrimeIndexRuns_unconditional hL

end OmegaBalance
