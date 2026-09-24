import OmegaBalance.Valuation

/-!
# The exact F₃ symmetry of twin primes

The main theorem is `f3_twin`: for primes `p, p+2` with `p > 3`,
`f3 (p+2) = -f3 p`, and BOTH values are nonzero.
The arithmetic core needs only `n > 1` and `n % 3 = 2`, not primality.
-/

namespace OmegaBalance

/-- The lower member of a twin-prime pair. The pair `(3,5)` is included. -/
def IsTwinPrime (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

instance (p : ℕ) : Decidable (IsTwinPrime p) :=
  inferInstanceAs (Decidable (p.Prime ∧ (p + 2).Prime))

theorem not_three_dvd_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : ¬ 3 ∣ p := by
  intro hd
  have := hp.eq_one_or_self_of_dvd 3 hd
  omega

theorem prime_mod_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hnd := not_three_dvd_prime hp h3
  have hm : p % 3 ≠ 0 := fun h => hnd (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

theorem twin_mod_three {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    p % 3 = 2 ∧ (p + 2) % 3 = 1 := by
  have hl := prime_mod_three hp h3
  have hr := prime_mod_three hq (by omega)
  omega

theorem twin_mod_six {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    p % 6 = 5 := by
  have hmod3 := (twin_mod_three hp hq h3).1
  have hmod2 := prime_mod_two_eq_one hp (by omega)
  omega

/-- The shared even neighbor of a nonexceptional twin pair is divisible by six. -/
theorem six_dvd_twin_center {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime)
    (h3 : 3 < p) : 6 ∣ p + 1 := by
  have hm := twin_mod_six hp hq h3
  apply Nat.dvd_iff_mod_eq_zero.mpr
  omega

/-- The usual `6k-1, 6k+1` parametrization, with `k > 0`. -/
theorem twin_six_mul_form {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    ∃ k : ℕ, 0 < k ∧ p = 6 * k - 1 ∧ p + 2 = 6 * k + 1 := by
  obtain ⟨k, hk⟩ := six_dvd_twin_center hp hq h3
  exact ⟨k, by omega, by omega, by omega⟩

/-- In residue class 2, only the RIGHT neighbor is divisible by three. -/
theorem f3_of_mod_three_two {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3 n = (v3 (n + 1) : ℤ) ∧ 0 < f3 n := by
  have hl : v3 (n - 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hr : 0 < v3 (n + 1) := by
    apply v3_pos_of_dvd (by omega)
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  constructor
  · simp [f3, neighborDiff, hl]
  · simp only [f3, neighborDiff, hl, Nat.cast_zero, sub_zero]
    exact_mod_cast hr

/-- In residue class 1, only the LEFT neighbor is divisible by three. -/
theorem f3_of_mod_three_one {n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) :
    f3 n = -(v3 (n - 1) : ℤ) ∧ f3 n < 0 := by
  have hr : v3 (n + 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hl : 0 < v3 (n - 1) := by
    apply v3_pos_of_dvd (by omega)
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  constructor
  · simp [f3, neighborDiff, hr]
  · have hc : (0 : ℤ) < (v3 (n - 1) : ℤ) := by exact_mod_cast hl
    simp only [f3, neighborDiff, hr, Nat.cast_zero, zero_sub]
    omega

/-- Every prime greater than three has nonzero F₃. -/
theorem f3_ne_zero_of_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : f3 p ≠ 0 := by
  rcases prime_mod_three hp h3 with hm | hm
  · exact ne_of_lt (f3_of_mod_three_one (by omega) hm).2
  · exact ne_of_gt (f3_of_mod_three_two (by omega) hm).2

theorem f3_pos_iff_mod_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    0 < f3 p ↔ p % 3 = 2 := by
  constructor
  · intro hpos
    rcases prime_mod_three hp h3 with hm | hm
    · have hneg := (f3_of_mod_three_one (by omega) hm).2
      omega
    · exact hm
  · intro hm
    exact (f3_of_mod_three_two (by omega) hm).2

theorem f3_neg_iff_mod_three {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    f3 p < 0 ↔ p % 3 = 1 := by
  constructor
  · intro hneg
    rcases prime_mod_three hp h3 with hm | hm
    · exact hm
    · have hpos := (f3_of_mod_three_two (by omega) hm).2
      omega
  · intro hm
    exact (f3_of_mod_three_one (by omega) hm).2

/-- The arithmetic core: primality is unnecessary for exact opposite values. -/
theorem f3_pair_values_of_mod_three {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3 n = (v3 (n + 1) : ℤ) ∧
    f3 (n + 2) = -(v3 (n + 1) : ℤ) ∧ 0 < v3 (n + 1) := by
  have hl := f3_of_mod_three_two hn hm
  have hr := f3_of_mod_three_one (n := n + 2) (by omega) (by omega)
  have he : n + 2 - 1 = n + 1 := by omega
  refine ⟨hl.1, ?_, ?_⟩
  · simpa only [he] using hr.1
  · have hc := hl.2
    rw [hl.1] at hc
    exact_mod_cast hc

theorem f3_opposite_of_mod_three {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3 (n + 2) = -f3 n ∧ f3 n ≠ 0 ∧ f3 (n + 2) ≠ 0 := by
  obtain ⟨hl, hr, hv⟩ := f3_pair_values_of_mod_three hn hm
  have hc : (0 : ℤ) < (v3 (n + 1) : ℤ) := by exact_mod_cast hv
  rw [hl, hr]
  omega

/-- Exact values, exposing the common magnitude for downstream arguments. -/
theorem f3_twin_values {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    f3 p = (v3 (p + 1) : ℤ) ∧
    f3 (p + 2) = -(v3 (p + 1) : ℤ) ∧ 0 < v3 (p + 1) :=
  f3_pair_values_of_mod_three (by omega) (twin_mod_three hp hq h3).1

/-- Main theorem: `F₃(p+2) = -F₃(p) ≠ 0` for twin primes above three. -/
theorem f3_twin {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    f3 (p + 2) = -f3 p ∧ f3 p ≠ 0 ∧ f3 (p + 2) ≠ 0 :=
  f3_opposite_of_mod_three (by omega) (twin_mod_three hp hq h3).1

theorem IsTwinPrime.f3_opposite {p : ℕ} (ht : IsTwinPrime p) (h3 : 3 < p) :
    f3 (p + 2) = -f3 p ∧ f3 p ≠ 0 ∧ f3 (p + 2) ≠ 0 :=
  f3_twin ht.1 ht.2 h3

theorem f3_twin_signs {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    0 < f3 p ∧ f3 (p + 2) < 0 := by
  obtain ⟨hl, hr, hv⟩ := f3_twin_values hp hq h3
  have hc : (0 : ℤ) < (v3 (p + 1) : ℤ) := by exact_mod_cast hv
  rw [hl, hr]
  omega

theorem f3_twin_abs_eq {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    |f3 (p + 2)| = |f3 p| := by
  rw [(f3_twin hp hq h3).1, abs_neg]

theorem f3_twin_natAbs_eq {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    (f3 (p + 2)).natAbs = (f3 p).natAbs := by
  rw [(f3_twin hp hq h3).1, Int.natAbs_neg]

theorem f3_twin_mul_neg {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    f3 p * f3 (p + 2) < 0 := by
  obtain ⟨hl, hr⟩ := f3_twin_signs hp hq h3
  exact mul_neg_of_pos_of_neg hl hr

end OmegaBalance
