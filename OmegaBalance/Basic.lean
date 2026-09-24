import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prime-neighbor factor counts

`bigOmega` counts prime factors WITH multiplicity, not distinct prime factors.
Differences are taken in `ℤ`: coercion must happen BEFORE subtraction.
The functions are total; `bigOmega 0 = 0` follows mathlib's convention.
Statements with their ordinary number-theoretic meaning include positivity hypotheses.
-/

namespace OmegaBalance

/-- The total number of prime factors, counted with multiplicity. -/
def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- A signed right-minus-left neighbor statistic. -/
def neighborDiff (f : ℕ → ℕ) (n : ℕ) : ℤ :=
  (f (n + 1) : ℤ) - (f (n - 1) : ℤ)

/-- `Ω(n+1) - Ω(n-1)`, with subtraction in the integers. -/
def omegaDiff (n : ℕ) : ℤ := neighborDiff bigOmega n

/-- The additive version `Ω(n-1) + Ω(n+1)`. -/
def omegaSum (n : ℕ) : ℕ := bigOmega (n - 1) + bigOmega (n + 1)

/-- Neighbor balance, independent of primality. -/
def IsOmegaBalanced (n : ℕ) : Prop := bigOmega (n - 1) = bigOmega (n + 1)

/-- An Ω-balanced prime. Primality is part of the predicate. -/
def IsOmegaBalancedPrime (p : ℕ) : Prop := p.Prime ∧ IsOmegaBalanced p

instance (n : ℕ) : Decidable (IsOmegaBalanced n) :=
  inferInstanceAs (Decidable (bigOmega (n - 1) = bigOmega (n + 1)))

instance (p : ℕ) : Decidable (IsOmegaBalancedPrime p) :=
  inferInstanceAs (Decidable (p.Prime ∧ IsOmegaBalanced p))

@[simp] theorem bigOmega_zero : bigOmega 0 = 0 := by simp [bigOmega]
@[simp] theorem bigOmega_one : bigOmega 1 = 0 := by simp [bigOmega]

@[simp] theorem bigOmega_prime {p : ℕ} (hp : p.Prime) : bigOmega p = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hp]

theorem bigOmega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simpa [bigOmega] using (Nat.perm_primeFactorsList_mul ha hb).length_eq

@[simp] theorem bigOmega_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    bigOmega (p ^ k) = k := by
  simp [bigOmega, hp.primeFactorsList_pow k]

theorem neighborDiff_eq_zero_iff (f : ℕ → ℕ) (n : ℕ) :
    neighborDiff f n = 0 ↔ f (n - 1) = f (n + 1) := by
  unfold neighborDiff
  omega

theorem neighborDiff_pos_iff (f : ℕ → ℕ) (n : ℕ) :
    0 < neighborDiff f n ↔ f (n - 1) < f (n + 1) := by
  unfold neighborDiff
  omega

theorem neighborDiff_neg_iff (f : ℕ → ℕ) (n : ℕ) :
    neighborDiff f n < 0 ↔ f (n + 1) < f (n - 1) := by
  unfold neighborDiff
  omega

@[simp] theorem omegaDiff_eq_zero_iff (n : ℕ) :
    omegaDiff n = 0 ↔ IsOmegaBalanced n :=
  neighborDiff_eq_zero_iff bigOmega n

theorem isOmegaBalancedPrime_iff (p : ℕ) :
    IsOmegaBalancedPrime p ↔ p.Prime ∧ omegaDiff p = 0 := by
  simp [IsOmegaBalancedPrime]

/-- The shared factor 2 cancels in the INTEGER difference. -/
theorem bigOmega_double_diff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (bigOmega (2 * b) : ℤ) - bigOmega (2 * a) =
      (bigOmega b : ℤ) - bigOmega a := by
  rw [bigOmega_mul (by omega) hb, bigOmega_mul (by omega) ha]
  simp only [Nat.cast_add]
  omega

theorem prime_mod_two_eq_one {p : ℕ} (hp : p.Prime) (h2 : 2 < p) :
    p % 2 = 1 := by
  have hnd : ¬ 2 ∣ p := by
    intro hd
    have := hp.eq_one_or_self_of_dvd 2 hd
    omega
  have hm : p % 2 ≠ 0 := fun h => hnd (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

/-- Halving both even neighbors does not change their Ω difference. -/
theorem omegaDiff_eq_half_diff {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) :
    omegaDiff n =
      (bigOmega ((n + 1) / 2) : ℤ) - bigOmega ((n - 1) / 2) := by
  have hl : 2 * ((n - 1) / 2) = n - 1 := by omega
  have hr : 2 * ((n + 1) / 2) = n + 1 := by omega
  have ha : (n - 1) / 2 ≠ 0 := by omega
  have hb : (n + 1) / 2 ≠ 0 := by omega
  simpa only [hl, hr, omegaDiff, neighborDiff] using bigOmega_double_diff ha hb

theorem omegaDiff_prime_eq_half_diff {p : ℕ} (hp : p.Prime) (h2 : 2 < p) :
    omegaDiff p =
      (bigOmega ((p + 1) / 2) : ℤ) - bigOmega ((p - 1) / 2) :=
  omegaDiff_eq_half_diff (by omega) (prime_mod_two_eq_one hp h2)

theorem isOmegaBalanced_iff_half {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) :
    IsOmegaBalanced n ↔ bigOmega ((n - 1) / 2) = bigOmega ((n + 1) / 2) := by
  rw [← omegaDiff_eq_zero_iff, omegaDiff_eq_half_diff hn hodd]
  omega

/-- The additive statistic is the Ω of the product of the neighbors. -/
theorem omegaSum_eq_bigOmega_product {n : ℕ} (hn : 1 < n) :
    omegaSum n = bigOmega ((n - 1) * (n + 1)) := by
  exact (bigOmega_mul (by omega) (by omega)).symm

/-- The product formulation can equally be written as `Ω(n²-1)`. -/
theorem omegaSum_eq_bigOmega_sq_sub_one {n : ℕ} (hn : 1 < n) :
    omegaSum n = bigOmega (n ^ 2 - 1) := by
  rw [omegaSum_eq_bigOmega_product hn]
  congr 1
  have hl : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hr : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel (by nlinarith)
  nlinarith

/-- The sum and difference recover the right count without division. -/
theorem omegaSum_add_omegaDiff (n : ℕ) :
    (omegaSum n : ℤ) + omegaDiff n = 2 * (bigOmega (n + 1) : ℤ) := by
  simp only [omegaSum, omegaDiff, neighborDiff, Nat.cast_add]
  ring

/-- The sum and difference recover the left count without division. -/
theorem omegaSum_sub_omegaDiff (n : ℕ) :
    (omegaSum n : ℤ) - omegaDiff n = 2 * (bigOmega (n - 1) : ℤ) := by
  simp only [omegaSum, omegaDiff, neighborDiff, Nat.cast_add]
  ring

end OmegaBalance
