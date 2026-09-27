import OmegaBalance.F3BFTBUnitResidues
import Mathlib.NumberTheory.PrimeCounting

namespace OmegaBalance

/-- Prime count through `x` in one arithmetic progression, in the same endpoint convention as Liu--Wang StandardBV. -/
def bftbPrimesInAP (x q l : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- Modulo one the unique residue class contains every prime, so the AP count is ordinary `π(x)`. -/
theorem bftbPrimesInAP_one_zero (x : ℕ) :
    bftbPrimesInAP x 1 0 = Nat.primeCounting x := by
  rw [bftbPrimesInAP, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  apply Finset.card_congr (Equiv.refl ℕ)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2, by simp [Nat.ModEq]⟩

/-- AP error with an arbitrary global main term; the Liu--Wang bridge later instantiates `main` with true Li. -/
noncomputable def bftbPrimeAPError
    (main : ℕ → ℝ) (x q l : ℕ) : ℝ :=
  (bftbPrimesInAP x q l : ℝ) - main x / (q.totient : ℝ)

/-- At modulus one the AP error is exactly the global prime-counting/main-term discrepancy. -/
theorem bftbPrimeAPError_one_zero (main : ℕ → ℝ) (x : ℕ) :
    bftbPrimeAPError main x 1 0 = (Nat.primeCounting x : ℝ) - main x := by
  simp [bftbPrimeAPError, bftbPrimesInAP_one_zero]

/-- Canonical-residue maximum of the generic AP error. -/
noncomputable def bftbCanonicalPrimeAPMaxError
    (main : ℕ → ℝ) (x q : ℕ) : ℝ :=
  bftbCanonicalResidueMax q (fun l => |bftbPrimeAPError main x q l|)

/-- The modulus-one maximum is exactly the absolute global discrepancy. -/
theorem bftbCanonicalPrimeAPMaxError_one
    (main : ℕ → ℝ) (x : ℕ) :
    bftbCanonicalPrimeAPMaxError main x 1 =
      |(Nat.primeCounting x : ℝ) - main x| := by
  simp [bftbCanonicalPrimeAPMaxError, bftbCanonicalResidueMax,
    bftbUnitResidues, bftbPrimeAPError_one_zero]

end OmegaBalance
