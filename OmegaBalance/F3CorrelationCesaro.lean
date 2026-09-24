import OmegaBalance.F3CorrelationLimit
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Arbitrary-length blocks for the truncated F₃ correlation

For a fixed cutoff `R`, the periodic retained correlation has period `3^R`.  This
module proves exact quotient/remainder decompositions for arbitrary initial lengths
and a uniform bound for the unfinished final block.  It does not yet exchange the
cutoff with the untruncated `F₃` limit.
-/

namespace OmegaBalance

open Function

/-- A residue indicator modulo `3^j` is periodic with any larger power-of-three
period. -/
theorem f3ModIndicator_periodic_pow_three {R j a : ℕ} (hj : j ≤ R) :
    Periodic (f3ModIndicator j a) (3 ^ R) := by
  intro n
  have hdiv : 3 ^ j ∣ (3 : ℕ) ^ R := pow_dvd_pow 3 hj
  have hz : (3 : ℕ) ^ R % 3 ^ j = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have heq : (n + 3 ^ R ≡ a [MOD 3 ^ j]) ↔ (n ≡ a [MOD 3 ^ j]) := by
    change (n + 3 ^ R) % 3 ^ j = a % 3 ^ j ↔ n % 3 ^ j = a % 3 ^ j
    rw [Nat.add_mod, hz]
    simp
  simp [f3ModIndicator, heq]

/-- Each signed residue layer inherits the complete `3^R` period. -/
theorem f3ResidueLayer_periodic_pow_three {R j : ℕ} (hj : j ≤ R) :
    Periodic (f3ResidueLayer j) (3 ^ R) := by
  intro n
  unfold f3ResidueLayer
  rw [f3ModIndicator_periodic_pow_three hj n,
    f3ModIndicator_periodic_pow_three hj n]

/-- The complete retained truncation is genuinely periodic, including the cyclic
boundary points where it differs from the natural-subtraction presentation. -/
theorem f3PeriodicTrunc_periodic (R : ℕ) :
    Periodic (f3PeriodicTrunc R) (3 ^ R) := by
  intro n
  unfold f3PeriodicTrunc
  apply Finset.sum_congr rfl
  intro j hj
  have hjR : j + 1 ≤ R := by
    have := Finset.mem_range.mp hj
    omega
  exact f3ResidueLayer_periodic_pow_three hjR n

/-- One summand of the fixed-cutoff periodic correlation. -/
def f3PeriodicCorrelationTerm (R h n : ℕ) : ℤ :=
  f3PeriodicTrunc R n * f3PeriodicTrunc R (n + h)

/-- The correlation summand has the same complete period as the retained function. -/
theorem f3PeriodicCorrelationTerm_periodic (R h : ℕ) :
    Periodic (f3PeriodicCorrelationTerm R h) (3 ^ R) := by
  simpa [f3PeriodicCorrelationTerm] using
    (f3PeriodicTrunc_periodic R).mul ((f3PeriodicTrunc_periodic R).add_const h)

/-- Exact block decomposition for an integer-valued periodic sequence. -/
theorem sum_range_periodic_mul_add_int {f : ℕ → ℤ} {P : ℕ}
    (hf : Periodic f P) (q r : ℕ) :
    (∑ n ∈ Finset.range (q * P + r), f n) =
      (q : ℤ) * (∑ n ∈ Finset.range P, f n) + ∑ n ∈ Finset.range r, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hlen : Nat.succ q * P + r = P + (q * P + r) := by
        simp [Nat.succ_mul, add_assoc, add_comm, add_left_comm]
      rw [hlen, Finset.sum_range_add]
      have hshift (i : ℕ) : f (P + i) = f i := by
        simpa [Nat.add_comm] using hf i
      simp_rw [hshift]
      rw [ih]
      push_cast
      ring

/-- Quotient/remainder form of the periodic block decomposition. -/
theorem sum_range_periodic_div_mod_int {f : ℕ → ℤ} {P : ℕ}
    (hf : Periodic f P) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) =
      (N / P : ℤ) * (∑ n ∈ Finset.range P, f n) +
        ∑ n ∈ Finset.range (N % P), f n := by
  have h := sum_range_periodic_mul_add_int hf (N / P) (N % P)
  rw [Nat.div_add_mod N P] at h
  exact h

/-- Arbitrary initial partial sum of the fixed-cutoff periodic correlation. -/
def f3PeriodicCorrelationPartialSum (R h N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, f3PeriodicCorrelationTerm R h n

/-- Any arbitrary length consists of full `3^R` periods plus one terminal block. -/
theorem f3PeriodicCorrelationPartialSum_eq_div_mod (R h N : ℕ) :
    f3PeriodicCorrelationPartialSum R h N =
      (N / 3 ^ R : ℤ) * f3PeriodicCorrelationSum R h +
        f3PeriodicCorrelationPartialSum R h (N % 3 ^ R) := by
  simpa [f3PeriodicCorrelationPartialSum, f3PeriodicCorrelationTerm,
    f3PeriodicCorrelationSum] using
    (sum_range_periodic_div_mod_int (f3PeriodicCorrelationTerm_periodic R h) N)

/-- A signed residue layer has magnitude at most one. -/
theorem abs_f3ResidueLayer_le_one (j n : ℕ) : |f3ResidueLayer j n| ≤ (1 : ℤ) := by
  unfold f3ResidueLayer f3ModIndicator
  by_cases hm : n ≡ 3 ^ j - 1 [MOD 3 ^ j] <;>
    by_cases hp : n ≡ 1 [MOD 3 ^ j] <;> simp [hm, hp]

/-- The retained periodic truncation has the trivial uniform bound `|F₃,R| ≤ R`. -/
theorem abs_f3PeriodicTrunc_le (R n : ℕ) :
    |f3PeriodicTrunc R n| ≤ (R : ℤ) := by
  unfold f3PeriodicTrunc
  calc
    |∑ j ∈ Finset.range R, f3ResidueLayer (j + 1) n| ≤
        ∑ j ∈ Finset.range R, |f3ResidueLayer (j + 1) n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range R, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro j _
      exact abs_f3ResidueLayer_le_one (j + 1) n
    _ = (R : ℤ) := by simp

/-- Every correlation summand is bounded by `R²`. -/
theorem abs_f3PeriodicCorrelationTerm_le (R h n : ℕ) :
    |f3PeriodicCorrelationTerm R h n| ≤ (R : ℤ) ^ 2 := by
  rw [f3PeriodicCorrelationTerm, abs_mul]
  have h₁ := abs_f3PeriodicTrunc_le R n
  have h₂ := abs_f3PeriodicTrunc_le R (n + h)
  have hm := mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity : (0 : ℤ) ≤ R)
  simpa [pow_two] using hm

/-- Any initial correlation block of length `N` is bounded by `N R²`. -/
theorem abs_f3PeriodicCorrelationPartialSum_le (R h N : ℕ) :
    |f3PeriodicCorrelationPartialSum R h N| ≤ (N : ℤ) * (R : ℤ) ^ 2 := by
  unfold f3PeriodicCorrelationPartialSum
  calc
    |∑ n ∈ Finset.range N, f3PeriodicCorrelationTerm R h n| ≤
        ∑ n ∈ Finset.range N, |f3PeriodicCorrelationTerm R h n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N, (R : ℤ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      exact abs_f3PeriodicCorrelationTerm_le R h n
    _ = (N : ℤ) * (R : ℤ) ^ 2 := by simp

/-- The unfinished quotient/remainder block is uniformly bounded independently of
`N`; this is the finite remainder estimate needed for the fixed-cutoff Cesàro limit. -/
theorem abs_f3PeriodicCorrelationRemainder_le (R h N : ℕ) :
    |f3PeriodicCorrelationPartialSum R h (N % 3 ^ R)| ≤
      ((3 : ℕ) ^ R : ℤ) * (R : ℤ) ^ 2 := by
  have h₁ := abs_f3PeriodicCorrelationPartialSum_le R h (N % 3 ^ R)
  have hp : 0 < (3 : ℕ) ^ R := pow_pos (by decide) R
  have hmod : N % 3 ^ R ≤ (3 : ℕ) ^ R := (Nat.mod_lt N hp).le
  have hcast : ((N % 3 ^ R : ℕ) : ℤ) ≤ ((3 : ℕ) ^ R : ℤ) := by
    exact_mod_cast hmod
  have h₂ : ((N % 3 ^ R : ℕ) : ℤ) * (R : ℤ) ^ 2 ≤
      ((3 : ℕ) ^ R : ℤ) * (R : ℤ) ^ 2 :=
    mul_le_mul_of_nonneg_right hcast (sq_nonneg (R : ℤ))
  exact h₁.trans h₂

end OmegaBalance
