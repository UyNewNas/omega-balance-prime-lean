import OmegaBalance.FactorSum
import Mathlib.Data.Finset.Card

/-!
# Finite counting transfer for prime-factor-sum balance

This module isolates the elementary injection used to transfer external
Ruth--Aaron counting estimates to prime centres.  No analytic estimate is
asserted here: any such bound remains an explicit hypothesis.

For an odd balanced prime `p`, the map `p ↦ (p - 1) / 2` lands among adjacent
indices `m` with `S(m) = S(m+1)`.  The map is injective because `p` is odd.
-/

namespace OmegaBalance

/-- S-balanced prime centres up to `X`.  The predicate is written out so the
finite set has a constructive decidability instance; the public membership
lemma below packages it back as `IsPrimeFactorSumBalancedPrime`. -/
def sumBalancedPrimesUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun p =>
    p.Prime ∧ primeFactorSum (p - 1) = primeFactorSum (p + 1)

/-- Positive Ruth--Aaron indices up to `X`, for the same factor sum `S`. -/
def ruthAaronIndicesUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun m =>
    0 < m ∧ primeFactorSum m = primeFactorSum (m + 1)

/-- Finite counting function for S-balanced prime centres. -/
def sumBalancedPrimeCount (X : ℕ) : ℕ := (sumBalancedPrimesUpTo X).card

/-- Finite Ruth--Aaron counting function for positive adjacent indices. -/
def ruthAaronCount (X : ℕ) : ℕ := (ruthAaronIndicesUpTo X).card

@[simp] theorem mem_sumBalancedPrimesUpTo {X p : ℕ} :
    p ∈ sumBalancedPrimesUpTo X ↔ p ≤ X ∧ IsPrimeFactorSumBalancedPrime p := by
  simp [sumBalancedPrimesUpTo, IsPrimeFactorSumBalancedPrime,
    IsPrimeFactorSumBalanced]

@[simp] theorem mem_ruthAaronIndicesUpTo {X m : ℕ} :
    m ∈ ruthAaronIndicesUpTo X ↔
      m ≤ X ∧ 0 < m ∧ primeFactorSum m = primeFactorSum (m + 1) := by
  simp [ruthAaronIndicesUpTo]

/-- The even prime is not an S-balanced prime centre. -/
theorem two_not_sumBalancedPrime : ¬ IsPrimeFactorSumBalancedPrime 2 := by
  intro h
  have hb := h.2
  have hb' : primeFactorSum 1 = primeFactorSum 3 := by
    simpa [IsPrimeFactorSumBalanced] using hb
  rw [primeFactorSum_one, primeFactorSum_prime (by norm_num : Nat.Prime 3)] at hb'
  omega

/-- The half-centre map sends every S-balanced prime `p ≤ X` to a positive
Ruth--Aaron index at most `(X-1)/2`. -/
theorem sumBalancedPrime_half_mem {X p : ℕ}
    (hp : p ∈ sumBalancedPrimesUpTo X) :
    (p - 1) / 2 ∈ ruthAaronIndicesUpTo ((X - 1) / 2) := by
  rw [mem_sumBalancedPrimesUpTo] at hp
  rcases hp with ⟨hpX, hpb⟩
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst p
    exact two_not_sumBalancedPrime hpb
  rcases hpb with ⟨hpp, hbal⟩
  have hp2 : 2 ≤ p := hpp.two_le
  have hpgt2 : 2 < p := by omega
  have hodd : p % 2 = 1 := prime_mod_two_eq_one hpp hpgt2
  have hhalf := (primeFactorSumBalanced_iff_half (by omega) hodd).mp hbal
  have hsucc : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  rw [mem_ruthAaronIndicesUpTo]
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.div_le_div_right (c := 2) (Nat.sub_le_sub_right hpX 1)
  · omega
  · simpa [hsucc] using hhalf

/-- The half-centre map is injective on S-balanced primes up to any bound. -/
theorem sumBalancedPrime_half_injOn (X : ℕ) :
    Set.InjOn (fun p : ℕ => (p - 1) / 2) (sumBalancedPrimesUpTo X : Set ℕ) := by
  intro p hp q hq heq
  have hp' : p ∈ sumBalancedPrimesUpTo X := by simpa using hp
  have hq' : q ∈ sumBalancedPrimesUpTo X := by simpa using hq
  rw [mem_sumBalancedPrimesUpTo] at hp' hq'
  have hpne2 : p ≠ 2 := by
    intro hp2
    subst p
    exact two_not_sumBalancedPrime hp'.2
  have hqne2 : q ≠ 2 := by
    intro hq2
    subst q
    exact two_not_sumBalancedPrime hq'.2
  have hp2 : 2 ≤ p := hp'.2.1.two_le
  have hq2 : 2 ≤ q := hq'.2.1.two_le
  have hpgt2 : 2 < p := by omega
  have hqgt2 : 2 < q := by omega
  have hpodd : p % 2 = 1 := prime_mod_two_eq_one hp'.2.1 hpgt2
  have hqodd : q % 2 = 1 := prime_mod_two_eq_one hq'.2.1 hqgt2
  have hpform : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hqform : 2 * ((q - 1) / 2) + 1 = q := by omega
  calc
    p = 2 * ((p - 1) / 2) + 1 := hpform.symm
    _ = 2 * ((q - 1) / 2) + 1 := by rw [heq]
    _ = q := hqform

/-- Elementary finite transfer: balanced prime centres inject into Ruth--Aaron
indices by `p ↦ (p-1)/2`. -/
theorem sumBalancedPrimeCount_le_ruthAaronCount (X : ℕ) :
    sumBalancedPrimeCount X ≤ ruthAaronCount ((X - 1) / 2) := by
  unfold sumBalancedPrimeCount ruthAaronCount
  apply Finset.card_le_card_of_injOn (fun p : ℕ => (p - 1) / 2)
  · intro p hp
    exact sumBalancedPrime_half_mem (by simpa using hp)
  · exact sumBalancedPrime_half_injOn X

/-- Pointwise external counting bounds transfer without becoming axioms of this
repository.  A Pomerance-style estimate can be supplied as `hB`; this theorem
only proves the elementary reduction. -/
theorem sumBalancedPrimeCount_le_of_ruthAaronBound
    (B : ℕ → ℕ) (hB : ∀ Y, ruthAaronCount Y ≤ B Y) (X : ℕ) :
    sumBalancedPrimeCount X ≤ B ((X - 1) / 2) :=
  (sumBalancedPrimeCount_le_ruthAaronCount X).trans (hB _)

end OmegaBalance
