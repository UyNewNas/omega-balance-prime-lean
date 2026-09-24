import OmegaBalance.F3SumProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite foundations for the correlation calculation

The capped valuation counts divisibility, including value R at zero. It must
not be confused with mathlib's totalized v3 0 = 0. These theorems prove exact
finite identities and periodicity, NOT the infinite Cesaro correlation limit.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Finite count of powers 3^1,...,3^R dividing n, valued in the integers. -/
def v3Trunc (R n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range R, if 3 ^ (j + 1) ∣ n then (1 : ℤ) else 0

/-- Truncated right-minus-left statistic. -/
def f3Trunc (R n : ℕ) : ℤ := v3Trunc R (n + 1) - v3Trunc R (n - 1)

theorem sum_initial_indicator (R d : ℕ) :
    (∑ j ∈ Finset.range R, if j < d then (1 : ℤ) else 0) = (min R d : ℕ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : R < d
    · have h1 : min R d = R := min_eq_left (by omega)
      have h2 : min (R + 1) d = R + 1 := min_eq_left (by omega)
      simp [h, h1, h2, Nat.succ_eq_add_one]
    · have h1 : min R d = d := min_eq_right (by omega)
      have h2 : min (R + 1) d = d := min_eq_right (by omega)
      simp [h, h1, h2, Nat.succ_eq_add_one]

/-- The exact finite indicator expansion, away from the ordinary singularity. -/
theorem v3Trunc_eq_min {n : ℕ} (hn : n ≠ 0) (R : ℕ) :
    v3Trunc R n = (min R (v3 n) : ℕ) := by
  have hd (j : ℕ) : 3 ^ (j + 1) ∣ n ↔ j < v3 n := by
    rw [v3_eq_padic, padicValNat_dvd_iff_le hn]
    omega
  unfold v3Trunc
  calc
    _ = ∑ j ∈ Finset.range R, if j < v3 n then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hd j]
    _ = (min R (v3 n) : ℕ) := sum_initial_indicator R (v3 n)

@[simp] theorem v3Trunc_zero (R : ℕ) : v3Trunc R 0 = (R : ℤ) := by
  simp [v3Trunc]

/-- Adding a multiple of the period preserves every retained divisibility layer. -/
theorem v3Trunc_translate {R n h : ℕ} (hd : 3 ^ R ∣ h) :
    v3Trunc R (n + h) = v3Trunc R n := by
  unfold v3Trunc
  apply Finset.sum_congr rfl
  intro j hj
  have hjR : j + 1 ≤ R := by have := Finset.mem_range.mp hj; omega
  have hdiv : 3 ^ (j + 1) ∣ h := (pow_dvd_pow 3 hjR).trans hd
  have he : 3 ^ (j + 1) ∣ n + h ↔ 3 ^ (j + 1) ∣ n := by
    constructor
    · intro hsum
      have hh := Nat.dvd_sub hsum hdiv
      simpa using hh
    · intro hn
      exact dvd_add hn hdiv
  rw [he]

theorem f3Trunc_periodic {n : ℕ} (hn : 1 ≤ n) (R : ℕ) :
    f3Trunc R (n + 3 ^ R) = f3Trunc R n := by
  have hp : n + 3 ^ R + 1 = (n + 1) + 3 ^ R := by omega
  have hm : n + 3 ^ R - 1 = (n - 1) + 3 ^ R := by omega
  rw [f3Trunc, hp, hm, v3Trunc_translate dvd_rfl, v3Trunc_translate dvd_rfl]
  rfl

theorem f3Trunc_eq_clipped {n : ℕ} (hn : 1 < n) (R : ℕ) :
    f3Trunc R n = (min R (v3 (n + 1)) : ℤ) - (min R (v3 (n - 1)) : ℤ) := by
  rw [f3Trunc, v3Trunc_eq_min (by omega), v3Trunc_eq_min (by omega)]

/-- Once both neighbor depths are retained the finite expansion is exact. -/
theorem f3Trunc_eq_f3 {n R : ℕ} (hn : 1 < n)
    (hp : v3 (n + 1) ≤ R) (hm : v3 (n - 1) ≤ R) :
    f3Trunc R n = f3 n := by
  rw [f3Trunc_eq_clipped hn R, min_eq_right hp, min_eq_right hm]
  rfl

/-- Exact telescoping of the untruncated statistic on an initial interval. -/
theorem f3_sum_range (N : ℕ) :
    (∑ i ∈ Finset.range N, f3 (i + 2)) = (v3 (N + 1) : ℤ) + v3 (N + 2) := by
  induction N with
  | zero =>
    have hz : v3 2 = 0 := v3_eq_zero_of_not_dvd (by decide)
    simp [hz]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    change (v3 (N + 1) : ℤ) + v3 (N + 2) +
      ((v3 (N + 3) : ℤ) - v3 (N + 2 - 1)) =
      (v3 (N + 2) : ℤ) + v3 (N + 3)
    rw [show N + 2 - 1 = N + 1 by omega]
    ring

end OmegaBalance
