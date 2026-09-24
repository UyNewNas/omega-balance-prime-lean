import OmegaBalance.F3SumProduct

/-!
# Normalized unit coordinates and exact cancellation

`f3Unit n = chi(n) * n` retains the full integer rather than just its depth.
This is a finite algebraic coordinate; it is NOT a definition of a p-adic logarithm.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The normalized signed integer, congruent to one at three on the unit domain. -/
def f3Unit (n : ℕ) : ℤ := -f3Side n * (n : ℤ)

theorem f3Unit_mul {m n : ℕ} (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3Unit (m * n) = f3Unit m * f3Unit n := by
  simp only [f3Unit, f3Side_mul hm3 hn3, Nat.cast_mul]
  ring

theorem f3Unit_sub_one_ne_zero {n : ℕ} (hn : 1 < n) : f3Unit n - 1 ≠ 0 := by
  rcases f3Side_values n with hs | hs <;> simp [f3Unit, hs] <;> omega

theorem f3Unit_depth {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    v3Int (f3Unit n - 1) = (f3 n).natAbs := by
  rcases f3Side_values n with hs | hs
  · have hid : f3Unit n - 1 = -((n : ℤ) + f3Side n) := by
      rw [f3Unit, hs]
      ring
    rw [hid, v3Int_neg, f3_center_valuation hn h3]
  · have hid : f3Unit n - 1 = (n : ℤ) + f3Side n := by
      rw [f3Unit, hs]
      ring
    rw [hid, f3_center_valuation hn h3]

/-- Integer valuation multiplicativity, with nonzero arguments. -/
theorem v3Int_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    v3Int (a * b) = v3Int a + v3Int b := by
  have h := padicValRat.mul (p := 3) (q := (a : ℚ)) (r := (b : ℚ))
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  simp only [← Int.cast_mul, ← v3Int_eq_padicValRat] at h
  exact_mod_cast h

@[simp] theorem v3Int_three_pow (k : ℕ) : v3Int ((3 : ℤ) ^ k) = k := by
  have h := v3Int_nat (3 ^ k)
  simpa using h

/-- The exact residual polynomial responsible for equal-level cancellation.
The coordinate equations imply the needed common divisibility; no prime assumption. -/
theorem f3_same_level_cancellation {m n k : ℕ} {a b : ℤ}
    (hm : 1 < m) (hn : 1 < n) (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n)
    (ha : f3Unit m = 1 + (3 : ℤ) ^ k * a)
    (hb : f3Unit n = 1 + (3 : ℤ) ^ k * b) :
    (f3 (m * n)).natAbs = k + v3Int (a + b + (3 : ℤ) ^ k * a * b) := by
  have hmn : 1 < m * n := by nlinarith
  have hmn3 : ¬ 3 ∣ m * n := by
    intro h
    rcases Nat.prime_three.dvd_mul.mp h with h | h
    · exact hm3 h
    · exact hn3 h
  have hid : f3Unit (m * n) - 1 =
      (3 : ℤ) ^ k * (a + b + (3 : ℤ) ^ k * a * b) := by
    rw [f3Unit_mul hm3 hn3, ha, hb]
    ring
  have hres : a + b + (3 : ℤ) ^ k * a * b ≠ 0 := by
    intro h
    have hz := f3Unit_sub_one_ne_zero hmn
    rw [hid, h, mul_zero] at hz
    exact hz rfl
  rw [← f3Unit_depth hmn hmn3, hid,
    v3Int_mul (pow_ne_zero _ (by decide)) hres, v3Int_three_pow]

/-- The first extra ternary digit decides whether cancellation starts. -/
theorem f3_same_level_rises_iff {m n k : ℕ} {a b : ℤ}
    (hm : 1 < m) (hn : 1 < n) (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) (hk : 0 < k)
    (ha : f3Unit m = 1 + (3 : ℤ) ^ k * a)
    (hb : f3Unit n = 1 + (3 : ℤ) ^ k * b) :
    k < (f3 (m * n)).natAbs ↔ (3 : ℤ) ∣ a + b := by
  have hmn : 1 < m * n := by nlinarith
  have hid : f3Unit (m * n) - 1 =
      (3 : ℤ) ^ k * (a + b + (3 : ℤ) ^ k * a * b) := by
    rw [f3Unit_mul hm3 hn3, ha, hb]
    ring
  have hres : a + b + (3 : ℤ) ^ k * a * b ≠ 0 := by
    intro h
    have hz := f3Unit_sub_one_ne_zero hmn
    rw [hid, h, mul_zero] at hz
    exact hz rfl
  have hdiv : (3 : ℤ) ∣ (3 : ℤ) ^ k * a * b :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) a) b
  have hv : 0 < v3Int (a + b + (3 : ℤ) ^ k * a * b) ↔
      (3 : ℤ) ∣ a + b + (3 : ℤ) ^ k * a * b := by
    simp only [v3Int, Nat.pos_iff_ne_zero, padicValInt.eq_zero_iff]
    simp [hres]
  rw [f3_same_level_cancellation hm hn hm3 hn3 ha hb]
  have hde : (3 : ℤ) ∣ a + b + (3 : ℤ) ^ k * a * b ↔ (3 : ℤ) ∣ a + b := by
    constructor
    · intro h
      have hh := dvd_sub h hdiv
      simpa using hh
    · intro h
      exact dvd_add h hdiv
  omega

end OmegaBalance
