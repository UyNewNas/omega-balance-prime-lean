import OmegaBalance.FactorSum
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

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
  change (p - 1) / 2 = (q - 1) / 2 at heq
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

/-- Finite counting function for all primes up to `X`. -/
def primeCountUpTo (X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter Nat.Prime).card

/-- Relative density of S-balanced primes among all primes up to `X`.
The value is totalized to zero when the denominator vanishes. -/
def sumBalancedPrimeRelativeDensity (X : ℕ) : ℝ :=
  (sumBalancedPrimeCount X : ℝ) / (primeCountUpTo X : ℝ)

/-- An indicator-weighted reciprocal sequence for positive Ruth--Aaron indices.
This lets external convergence results be supplied without asserting them as
axioms of this repository. -/
def ruthAaronReciprocal (m : ℕ) : ℝ :=
  if 0 < m ∧ primeFactorSum m = primeFactorSum (m + 1) then
    1 / (m : ℝ)
  else
    0

/-- The type of S-balanced prime centres, used for reciprocal-series transfer. -/
abbrev SumBalancedPrime := {p : ℕ // IsPrimeFactorSumBalancedPrime p}

/-- Pointwise external counting bounds transfer without becoming axioms of this
repository.  A Pomerance-style estimate can be supplied as `hB`; this theorem
only proves the elementary reduction. -/
theorem sumBalancedPrimeCount_le_of_ruthAaronBound
    (B : ℕ → ℕ) (hB : ∀ Y, ruthAaronCount Y ≤ B Y) (X : ℕ) :
    sumBalancedPrimeCount X ≤ B ((X - 1) / 2) :=
  (sumBalancedPrimeCount_le_ruthAaronCount X).trans (hB _)

/-- Any explicit majorant whose ratio to the prime counting function tends to
zero transfers that relative-density-zero conclusion to S-balanced primes.
The asymptotic input remains a theorem hypothesis. -/
theorem sumBalancedPrime_relativeDensity_zero_of_majorant
    (B : ℕ → ℕ)
    (hB : ∀ X, sumBalancedPrimeCount X ≤ B X)
    (hzero : Filter.Tendsto
      (fun X : ℕ => (B X : ℝ) / (primeCountUpTo X : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto sumBalancedPrimeRelativeDensity Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro X
    unfold sumBalancedPrimeRelativeDensity
    positivity
  · intro X
    unfold sumBalancedPrimeRelativeDensity
    exact div_le_div_of_nonneg_right (by exact_mod_cast hB X) (by positivity)
  · exact hzero

/-- Pomerance-style Ruth--Aaron counting bounds transfer to zero relative
prime density once the corresponding analytic majorant limit (for example,
from that bound together with the prime number theorem) is supplied. -/
theorem sumBalancedPrime_relativeDensity_zero_of_ruthAaronBound
    (B : ℕ → ℕ)
    (hB : ∀ Y, ruthAaronCount Y ≤ B Y)
    (hzero : Filter.Tendsto
      (fun X : ℕ => (B ((X - 1) / 2) : ℝ) / (primeCountUpTo X : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto sumBalancedPrimeRelativeDensity Filter.atTop (nhds 0) := by
  apply sumBalancedPrime_relativeDensity_zero_of_majorant
      (B := fun X => B ((X - 1) / 2))
  · intro X
    exact sumBalancedPrimeCount_le_of_ruthAaronBound B hB X
  · exact hzero

/-- The half-centre map is globally injective on the subtype of S-balanced
prime centres. -/
theorem sumBalancedPrime_half_injective :
    Function.Injective (fun p : SumBalancedPrime => (p.1 - 1) / 2) := by
  intro p q hhalf
  let X := max p.1 q.1
  have hp_mem : p.1 ∈ sumBalancedPrimesUpTo X := by
    rw [mem_sumBalancedPrimesUpTo]
    exact ⟨Nat.le_max_left _ _, p.property⟩
  have hq_mem : q.1 ∈ sumBalancedPrimesUpTo X := by
    rw [mem_sumBalancedPrimesUpTo]
    exact ⟨Nat.le_max_right _ _, q.property⟩
  apply Subtype.ext
  exact (sumBalancedPrime_half_injOn X) (by simpa using hp_mem)
    (by simpa using hq_mem) hhalf

/-- Each reciprocal of an S-balanced prime is bounded by the reciprocal of
its positive Ruth--Aaron half-index. -/
theorem sumBalancedPrime_reciprocal_le_ruthAaron (p : SumBalancedPrime) :
    (1 : ℝ) / (p.1 : ℝ) ≤ ruthAaronReciprocal ((p.1 - 1) / 2) := by
  have hp_mem : p.1 ∈ sumBalancedPrimesUpTo p.1 := by
    rw [mem_sumBalancedPrimesUpTo]
    exact ⟨le_rfl, p.property⟩
  have hm_mem := sumBalancedPrime_half_mem hp_mem
  rw [mem_ruthAaronIndicesUpTo] at hm_mem
  have hcond :
      0 < (p.1 - 1) / 2 ∧
        primeFactorSum ((p.1 - 1) / 2) =
          primeFactorSum ((p.1 - 1) / 2 + 1) :=
    ⟨hm_mem.2.1, hm_mem.2.2⟩
  rw [ruthAaronReciprocal, if_pos hcond]
  apply one_div_le_one_div_of_le
  · exact_mod_cast hm_mem.2.1
  · exact_mod_cast (show (p.1 - 1) / 2 ≤ p.1 by omega)

/-- Convergence of the reciprocal series over positive Ruth--Aaron indices
transfers to convergence of the reciprocal series over S-balanced primes.
Pomerance's analytic convergence theorem can be supplied as `hRA`; it is not
reintroduced here as an axiom. -/
theorem summable_sumBalancedPrime_reciprocals_of_ruthAaron
    (hRA : Summable ruthAaronReciprocal) :
    Summable (fun p : SumBalancedPrime => (1 : ℝ) / (p.1 : ℝ)) := by
  have hmajor : Summable (fun p : SumBalancedPrime =>
      ruthAaronReciprocal ((p.1 - 1) / 2)) :=
    hRA.comp_injective sumBalancedPrime_half_injective
  refine Summable.of_nonneg_of_le (fun p => by positivity) ?_ hmajor
  intro p
  exact sumBalancedPrime_reciprocal_le_ruthAaron p

end OmegaBalance
