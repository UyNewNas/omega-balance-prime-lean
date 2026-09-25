import OmegaBalance.F3Infinitude
import Mathlib.Data.Finset.Max

/-!
# Sign changes between consecutive primes

Consecutive means consecutive in the FULL prime sequence: no prime lies
strictly between the endpoints. Both directions occur arbitrarily far out.
The magnitudes at a crossing are not asserted to match, and no bound on
the distance between the primes is asserted.
-/

namespace OmegaBalance

/-- Adjacency in the full prime sequence, without a filtered-subsequence convention. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

/-- Select the first prime of opposite sign, and the largest prime below it. -/
theorem f3_crossing_after_prime {a : ℕ} {s : ℤ}
    (ha : a.Prime) (ha3 : 3 < a) (hs : s = 1 ∨ s = -1)
    (haPos : 0 < s * f3 a)
    (hex : ∃ q : ℕ, a < q ∧ q.Prime ∧ s * f3 q < 0) :
    ∃ p q : ℕ, a ≤ p ∧ ConsecutivePrimes p q ∧
      0 < s * f3 p ∧ s * f3 q < 0 := by
  classical
  let q := Nat.find hex
  have hq : a < q ∧ q.Prime ∧ s * f3 q < 0 := Nat.find_spec hex
  let P : Finset ℕ := (Finset.range q).filter Nat.Prime
  have haP : a ∈ P := by simp [P, ha, hq.1]
  have hP : P.Nonempty := ⟨a, haP⟩
  let p := P.max' hP
  have hpP : p ∈ P := Finset.max'_mem P hP
  have hpp : p.Prime := (Finset.mem_filter.mp hpP).2
  have hpq : p < q := Finset.mem_range.mp (Finset.mem_filter.mp hpP).1
  have hap : a ≤ p := Finset.le_max' P a haP
  have hcon : ConsecutivePrimes p q := by
    refine ⟨hpp, hq.2.1, hpq, ?_⟩
    intro r hpr hrq hrp
    have hrP : r ∈ P := by simp [P, hrq, hrp]
    have hrle : r ≤ p := Finset.le_max' P r hrP
    omega
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> omega
  have hf0 : s * f3 p ≠ 0 :=
    mul_ne_zero hs0 (f3_ne_zero_of_prime hpp (by omega))
  have hpNonneg : 0 ≤ s * f3 p := by
    by_contra h
    have hneg : s * f3 p < 0 := by omega
    by_cases he : p = a
    · rw [he] at hneg
      omega
    · have hpAfter : a < p := by omega
      have hqp : q ≤ p := Nat.find_min' hex ⟨hpAfter, hpp, hneg⟩
      omega
  exact ⟨p, q, hap, hcon, by omega, hq.2.2⟩

/-- Positive-to-negative transitions between genuine consecutive primes are unbounded. -/
theorem exists_consecutive_primes_f3_pos_neg (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ 3 < p ∧ ConsecutivePrimes p q ∧
      0 < f3 p ∧ f3 q < 0 := by
  obtain ⟨a, hB, ha3, ha, hfa⟩ := exists_prime_gt_f3_pos (k := 1) (by decide) B
  have hex : ∃ q : ℕ, a < q ∧ q.Prime ∧ (1 : ℤ) * f3 q < 0 := by
    obtain ⟨q, haq, _, hq, hfq⟩ := exists_prime_gt_f3_neg (k := 1) (by decide) a
    exact ⟨q, haq, hq, by simpa [hfq]⟩
  obtain ⟨p, q, hap, hcon, hp, hq⟩ :=
    f3_crossing_after_prime ha ha3 (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
      (by simpa [hfa]) hex
  exact ⟨p, q, by omega, by omega, hcon, by simpa using hp, by simpa using hq⟩

/-- The reverse direction also occurs arbitrarily far out. -/
theorem exists_consecutive_primes_f3_neg_pos (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ 3 < p ∧ ConsecutivePrimes p q ∧
      f3 p < 0 ∧ 0 < f3 q := by
  obtain ⟨a, hB, ha3, ha, hfa⟩ := exists_prime_gt_f3_neg (k := 1) (by decide) B
  have hex : ∃ q : ℕ, a < q ∧ q.Prime ∧ (-1 : ℤ) * f3 q < 0 := by
    obtain ⟨q, haq, _, hq, hfq⟩ := exists_prime_gt_f3_pos (k := 1) (by decide) a
    exact ⟨q, haq, hq, by simpa [hfq]⟩
  obtain ⟨p, q, hap, hcon, hp, hq⟩ :=
    f3_crossing_after_prime ha ha3 (Or.inr rfl : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1)
      (by simpa [hfa]) hex
  simp only [neg_one_mul] at hp hq
  exact ⟨p, q, by omega, by omega, hcon, by omega, by omega⟩

/-- Infinitely many left endpoints of positive-to-negative consecutive crossings. -/
theorem f3_consecutive_pos_neg_infinite :
    {p : ℕ | 3 < p ∧ ∃ q, ConsecutivePrimes p q ∧ 0 < f3 p ∧ f3 q < 0}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨p, q, hB, hp3, hcon, hp, hq⟩ := exists_consecutive_primes_f3_pos_neg B
  exact ⟨p, ⟨hp3, q, hcon, hp, hq⟩, hB⟩

/-- Infinitely many left endpoints of negative-to-positive consecutive crossings. -/
theorem f3_consecutive_neg_pos_infinite :
    {p : ℕ | 3 < p ∧ ∃ q, ConsecutivePrimes p q ∧ f3 p < 0 ∧ 0 < f3 q}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨p, q, hB, hp3, hcon, hp, hq⟩ := exists_consecutive_primes_f3_neg_pos B
  exact ⟨p, ⟨hp3, q, hcon, hp, hq⟩, hB⟩

/-- A compact sign-change statement; it does not impose equal absolute values. -/
theorem f3_consecutive_sign_changes_infinite :
    {p : ℕ | 3 < p ∧ ∃ q, ConsecutivePrimes p q ∧ f3 p * f3 q < 0}.Infinite := by
  apply f3_consecutive_pos_neg_infinite.mono
  intro p hp
  obtain ⟨hp3, q, hcon, hpos, hneg⟩ := hp
  exact ⟨hp3, q, hcon, mul_neg_of_pos_of_neg hpos hneg⟩

end OmegaBalance
