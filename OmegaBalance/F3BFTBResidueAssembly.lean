import OmegaBalance.F3BFTBResidueBlock
import OmegaBalance.F3BFTBPigeonhole

namespace OmegaBalance

/--
An exact prime pattern inside a protected tuple extends to the whole finite
ambient interval whenever every ambient offset outside the tuple is composite,
uniformly in the translation parameter.
-/
theorem bftb_full_exact_prime_pattern_infinite_of_outside_composite
    {value : ℕ → ℕ → ℕ} {I H S : Finset ℕ}
    (hSH : S ⊆ H)
    (hinf : (BFTBExactPrimePatternSet value H S).Infinite)
    (hout : ∀ n : ℕ, ∀ u ∈ I, u ∉ H → ¬ (value n u).Prime) :
    ({n : ℕ | ∀ u ∈ I, (value n u).Prime ↔ u ∈ S} : Set ℕ).Infinite := by
  apply hinf.mono
  intro n hn
  change ∀ u ∈ I, (value n u).Prime ↔ u ∈ S
  exact bftb_exact_prime_pattern_extend hSH hn (hout n)

/--
Finite BFTB assembly lemma.  If infinitely many translations contain at least
L primes in a protected affine tuple, and every offset of the surrounding
interval outside that tuple is uniformly composite, then one obtains
arbitrarily far genuine bounded consecutive-prime blocks of length L in the
prescribed residue class.

The only infinitary input here is the explicit many-primes hypothesis; this
lemma does not assume a BFTB/Shiu consecutive-prime conclusion.
-/
theorem bftb_consecutivePrimeRunsInClassBounded_of_many_primes_and_outside
    {a D g lo hi L : ℕ} {H : Finset ℕ}
    (hg : 0 < g)
    (hHI : H ⊆ Finset.Icc lo hi)
    (hDg : D ∣ g)
    (hres : ∀ h ∈ H, h ≡ a [MOD D])
    (hmany :
      (BFTBAtLeastPrimeCountSet
        (fun n u => g * n + u) H L).Infinite)
    (hout : ∀ n : ℕ, ∀ u ∈ Finset.Icc lo hi, u ∉ H →
      ¬ (g * n + u).Prime) :
    ∀ B : ℕ,
      ConsecutivePrimeRunInClassBounded a D L B (hi - lo) := by
  obtain ⟨S, hSH, hLS, hExactH⟩ :=
    bftb_exists_large_exact_prime_pattern
      (fun n u => g * n + u) H hmany
  have hSI : S ⊆ Finset.Icc lo hi :=
    hSH.trans hHI
  have hresS : ∀ u ∈ S, u ≡ a [MOD D] := by
    intro u hu
    exact hres u (hSH hu)
  have hFull :
      ({n : ℕ | ∀ u ∈ Finset.Icc lo hi,
        (g * n + u).Prime ↔ u ∈ S} : Set ℕ).Infinite :=
    bftb_full_exact_prime_pattern_infinite_of_outside_composite
      hSH hExactH hout
  exact bftb_consecutivePrimeRunsInClassBounded_of_infinite_exact_prefix
    hg hLS hSI hDg hresS hFull

end OmegaBalance
