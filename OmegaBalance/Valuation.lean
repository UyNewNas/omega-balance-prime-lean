import OmegaBalance.Basic

/-!
# Prime-valuation neighbor statistics

`valuation q n` is mathlib's `n.factorization q`. For prime `q` and positive `n`
this is the exponent of `q` in `n`. The totalized value at zero is zero, NOT
an infinite valuation. Theorems requiring the ordinary valuation assume `n ≠ 0`.
-/

namespace OmegaBalance

/-- Prime factor multiplicity; zero at `n = 0` and at nonprime `q`. -/
def valuation (q n : ℕ) : ℕ := n.factorization q

/-- A local component of the signed neighbor statistic. -/
def valuationDiff (q n : ℕ) : ℤ := neighborDiff (valuation q) n

/-- The exponent of 3 in a positive natural number; totalized to zero at zero. -/
def v3 (n : ℕ) : ℕ := valuation 3 n

/-- `v₃(n+1) - v₃(n-1)`, computed in `ℤ`. -/
def f3 (n : ℕ) : ℤ := neighborDiff v3 n

theorem f3_eq_valuationDiff (n : ℕ) : f3 n = valuationDiff 3 n := rfl

theorem valuation_eq_padicValNat {q : ℕ} (hq : q.Prime) (n : ℕ) :
    valuation q n = padicValNat q n := Nat.factorization_def n hq

@[simp] theorem valuation_zero (q : ℕ) : valuation q 0 = 0 := by
  simp [valuation]

@[simp] theorem valuation_one (q : ℕ) : valuation q 1 = 0 := by
  simp [valuation]

theorem valuation_eq_zero_of_not_dvd {q n : ℕ} (h : ¬ q ∣ n) :
    valuation q n = 0 := Nat.factorization_eq_zero_of_not_dvd h

theorem valuation_pos_of_dvd {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) (hd : q ∣ n) :
    0 < valuation q n := hq.factorization_pos_of_dvd hn hd

theorem valuation_pos_iff_dvd {q n : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    0 < valuation q n ↔ q ∣ n := by
  constructor
  · intro h
    exact Nat.dvd_of_factorization_pos (Nat.ne_of_gt h)
  · exact valuation_pos_of_dvd hq hn

theorem valuation_mul (q : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    valuation q (a * b) = valuation q a + valuation q b := by
  simp only [valuation, Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem valuation_prime_pow {q : ℕ} (hq : q.Prime) (k : ℕ) :
    valuation q (q ^ k) = k := Nat.factorization_pow_self hq

@[simp] theorem v3_zero : v3 0 = 0 := valuation_zero 3
@[simp] theorem v3_one : v3 1 = 0 := valuation_one 3

theorem v3_eq_zero_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : v3 n = 0 :=
  valuation_eq_zero_of_not_dvd h

theorem v3_pos_of_dvd {n : ℕ} (hn : n ≠ 0) (hd : 3 ∣ n) : 0 < v3 n :=
  valuation_pos_of_dvd Nat.prime_three hn hd

theorem v3_pos_iff_dvd {n : ℕ} (hn : n ≠ 0) : 0 < v3 n ↔ 3 ∣ n :=
  valuation_pos_iff_dvd Nat.prime_three hn

theorem v3_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    v3 (a * b) = v3 a + v3 b := valuation_mul 3 ha hb

@[simp] theorem v3_pow_three (k : ℕ) : v3 (3 ^ k) = k :=
  valuation_prime_pow Nat.prime_three k

end OmegaBalance
