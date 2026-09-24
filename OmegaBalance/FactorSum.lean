import OmegaBalance.Valuation
import Mathlib.Tactic

/-!
# Prime factor SUMS with multiplicity

`primeFactorSum` is the sum of the prime-factor list, not its length and
not `omegaSum`. All signed differences and defects are integers.
The value at zero is totalized to zero, following `Nat.primeFactorsList`.
-/

namespace OmegaBalance

/-- Sum of prime factors WITH multiplicity. -/
def primeFactorSum (n : ℕ) : ℕ := n.primeFactorsList.sum

/-- The signed statistic `S(n+1) - S(n-1)`. -/
def primeFactorSumDiff (n : ℕ) : ℤ := neighborDiff primeFactorSum n

/-- Neighbor balance for the sum of the prime factors. -/
def IsPrimeFactorSumBalanced (n : ℕ) : Prop :=
  primeFactorSum (n - 1) = primeFactorSum (n + 1)

/-- Primality is an explicit part of this predicate. -/
def IsPrimeFactorSumBalancedPrime (p : ℕ) : Prop :=
  p.Prime ∧ IsPrimeFactorSumBalanced p

/-- Simultaneous sum balance and count balance at the specified level. -/
def IsDoubleBalancedPrime (p k : ℕ) : Prop :=
  p.Prime ∧ IsPrimeFactorSumBalanced p ∧
    bigOmega (p - 1) = k ∧ bigOmega (p + 1) = k

/-- The INTEGER defect `n - S(n)`. -/
def primeFactorDefect (n : ℕ) : ℤ := (n : ℤ) - primeFactorSum n

@[simp] theorem primeFactorSum_zero : primeFactorSum 0 = 0 := by
  simp [primeFactorSum]

@[simp] theorem primeFactorSum_one : primeFactorSum 1 = 0 := by
  simp [primeFactorSum]

@[simp] theorem primeFactorSum_prime {p : ℕ} (hp : p.Prime) :
    primeFactorSum p = p := by
  simp [primeFactorSum, Nat.primeFactorsList_prime hp]

theorem primeFactorSum_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeFactorSum (a * b) = primeFactorSum a + primeFactorSum b := by
  simpa [primeFactorSum, List.sum_append] using
    (Nat.perm_primeFactorsList_mul ha hb).sum_eq

@[simp] theorem primeFactorSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeFactorSum (p ^ k) = k * p := by
  simp [primeFactorSum, hp.primeFactorsList_pow k, List.sum_replicate]

/-- A kernel-checkable factorization certificate may contain repeated primes. -/
theorem primeFactorSum_of_factors {n : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, p.Prime) :
    primeFactorSum n = l.sum := by
  exact (Nat.primeFactorsList_unique hprod hprime).sum_eq.symm

theorem bigOmega_of_factors {n : ℕ} {l : List ℕ}
    (hprod : l.prod = n) (hprime : ∀ p ∈ l, p.Prime) :
    bigOmega n = l.length := by
  exact (Nat.primeFactorsList_unique hprod hprime).length_eq.symm

@[simp] theorem primeFactorSumDiff_eq_zero_iff (n : ℕ) :
    primeFactorSumDiff n = 0 ↔ IsPrimeFactorSumBalanced n :=
  neighborDiff_eq_zero_iff primeFactorSum n

theorem isPrimeFactorSumBalancedPrime_iff (p : ℕ) :
    IsPrimeFactorSumBalancedPrime p ↔ p.Prime ∧ primeFactorSumDiff p = 0 := by
  simp [IsPrimeFactorSumBalancedPrime]

theorem primeFactorSum_double_diff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (primeFactorSum (2 * b) : ℤ) - primeFactorSum (2 * a) =
      (primeFactorSum b : ℤ) - primeFactorSum a := by
  rw [primeFactorSum_mul (by omega) hb, primeFactorSum_mul (by omega) ha]
  push_cast
  ring

theorem primeFactorSumDiff_eq_half_diff {n : ℕ} (hn : 1 < n)
    (hodd : n % 2 = 1) :
    primeFactorSumDiff n =
      (primeFactorSum ((n + 1) / 2) : ℤ) - primeFactorSum ((n - 1) / 2) := by
  have hl : 2 * ((n - 1) / 2) = n - 1 := by omega
  have hr : 2 * ((n + 1) / 2) = n + 1 := by omega
  have ha : (n - 1) / 2 ≠ 0 := by omega
  have hb : (n + 1) / 2 ≠ 0 := by omega
  simpa only [hl, hr, primeFactorSumDiff, neighborDiff] using
    primeFactorSum_double_diff ha hb

theorem primeFactorSumDiff_prime_eq_half_diff {p : ℕ}
    (hp : p.Prime) (h2 : 2 < p) :
    primeFactorSumDiff p =
      (primeFactorSum ((p + 1) / 2) : ℤ) - primeFactorSum ((p - 1) / 2) :=
  primeFactorSumDiff_eq_half_diff (by omega) (prime_mod_two_eq_one hp h2)

theorem primeFactorSumBalanced_iff_half {n : ℕ} (hn : 1 < n)
    (hodd : n % 2 = 1) :
    IsPrimeFactorSumBalanced n ↔
      primeFactorSum ((n - 1) / 2) = primeFactorSum ((n + 1) / 2) := by
  rw [← primeFactorSumDiff_eq_zero_iff, primeFactorSumDiff_eq_half_diff hn hodd]
  omega

/-- Lists here encode products, not a claim that the center is prime. -/
theorem primeFactorSum_center_iff {m : ℕ} (hm : 0 < m) :
    IsPrimeFactorSumBalanced (2 * m + 1) ↔ primeFactorSum m = primeFactorSum (m + 1) := by
  rw [primeFactorSumBalanced_iff_half (by omega) (by omega)]
  congr 1 <;> omega

/-- Coprime, adjacent cofactors give a general construction certificate. -/
theorem primeFactorSum_cofactor_construction {A B q r : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hadj : B * r = A * q + 1)
    (hsum : primeFactorSum A + q = primeFactorSum B + r)
    (hp : (2 * (A * q) + 1).Prime) :
    IsPrimeFactorSumBalancedPrime (2 * (A * q) + 1) := by
  refine ⟨hp, (primeFactorSum_center_iff (Nat.mul_pos (Nat.pos_of_ne_zero hA) hq.pos)).2 ?_⟩
  rw [← hadj, primeFactorSum_mul hA hq.ne_zero, primeFactorSum_mul hB hr.ne_zero,
    primeFactorSum_prime hq, primeFactorSum_prime hr]
  exact hsum

/-- Removing the prime-value restriction on q,r leaves an exact defect identity. -/
theorem primeFactorSum_cofactor_defect {A B q r : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hadj : B * r = A * q + 1)
    (hsum : (q : ℤ) - r = (primeFactorSum B : ℤ) - primeFactorSum A) :
    primeFactorSumDiff (2 * (A * q) + 1) = primeFactorDefect q - primeFactorDefect r := by
  have hm : 0 < A * q := Nat.mul_pos (Nat.pos_of_ne_zero hA) (Nat.pos_of_ne_zero hq)
  have hl : (2 * (A * q) + 1 - 1) = 2 * (A * q) := by omega
  have he : (2 * (A * q) + 1 + 1) = 2 * (B * r) := by omega
  unfold primeFactorSumDiff neighborDiff
  rw [hl, he, primeFactorSum_double_diff (mul_ne_zero hA hq) (mul_ne_zero hB hr),
    primeFactorSum_mul hA hq, primeFactorSum_mul hB hr]
  simp only [primeFactorDefect, Nat.cast_add]
  omega

/-- The two kinds of balance are deliberately independent predicates. -/
theorem doubleBalanced_sumBalanced {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    IsPrimeFactorSumBalancedPrime p := ⟨h.1, h.2.1⟩

theorem doubleBalanced_omegaBalanced {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    IsOmegaBalancedPrime p := ⟨h.1, h.2.2.1.trans h.2.2.2.symm⟩

theorem doubleBalanced_omegaSum {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    omegaSum p = 2 * k := by
  simp [omegaSum, h.2.2.1, h.2.2.2, two_mul]

/-- Double-balanced twin partners must have the same count level. -/
theorem doubleBalanced_twin_same_level {p k j : ℕ}
    (h : IsDoubleBalancedPrime p k) (h' : IsDoubleBalancedPrime (p + 2) j) : k = j := by
  have he : p + 2 - 1 = p + 1 := by omega
  have hl := h.2.2.2
  have hr := h'.2.2.1
  rw [he] at hr
  omega

end OmegaBalance
