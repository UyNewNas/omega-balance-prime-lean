import OmegaBalance.F3CorrelationCesaroLimit

/-!
# Pointwise tail identities for the F₃ correlation

This module starts the `L²` tail stage of the correlation proof.  It separates the
untruncated statistic from its retained cutoff and proves exact pointwise formulas
for the error.  No Cesàro tail bound or cutoff/limit exchange is asserted here yet.
-/

namespace OmegaBalance

/-- Excess three-adic depth beyond a retained cutoff. -/
def v3Excess (R n : ℕ) : ℕ := v3 n - R

/-- Pointwise difference between the genuine statistic and its divisibility cutoff. -/
def f3Tail (R n : ℕ) : ℤ := f3 n - f3Trunc R n

/-- In residue class zero modulo three, both neighboring valuations vanish, so the
truncation error is exactly zero. -/
theorem f3Tail_of_mod_three_zero {R n : ℕ} (hn : 1 < n) (hm : n % 3 = 0) :
    f3Tail R n = 0 := by
  have hl : v3 (n - 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  have hr : v3 (n + 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [f3Tail, f3_of_mod_three_zero hn hm, f3Trunc_eq_clipped hn R, hl, hr]
  simp

/-- In residue class two modulo three, the tail is the positive excess depth of the
right neighbor. -/
theorem f3Tail_of_mod_three_two {R n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3Tail R n = (v3Excess R (n + 1) : ℤ) := by
  have hl : v3 (n - 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [f3Tail, (f3_of_mod_three_two hn hm).1, f3Trunc_eq_clipped hn R, hl]
  simp only [min_eq_zero, Nat.cast_zero, sub_zero, v3Excess]
  by_cases hR : R ≤ v3 (n + 1)
  · rw [min_eq_left hR, Nat.cast_sub hR]
  · have hdR : v3 (n + 1) ≤ R := by omega
    rw [min_eq_right hdR]
    have hz : v3 (n + 1) - R = 0 := Nat.sub_eq_zero_of_le hdR
    rw [hz]
    simp

/-- In residue class one modulo three, the tail is the negative excess depth of the
left neighbor. -/
theorem f3Tail_of_mod_three_one {R n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) :
    f3Tail R n = -(v3Excess R (n - 1) : ℤ) := by
  have hr : v3 (n + 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [f3Tail, (f3_of_mod_three_one hn hm).1, f3Trunc_eq_clipped hn R, hr]
  simp only [min_eq_zero, Nat.cast_zero, zero_sub, v3Excess]
  by_cases hR : R ≤ v3 (n - 1)
  · rw [min_eq_left hR, Nat.cast_sub hR]
    ring
  · have hdR : v3 (n - 1) ≤ R := by omega
    rw [min_eq_right hdR]
    have hz : v3 (n - 1) - R = 0 := Nat.sub_eq_zero_of_le hdR
    rw [hz]
    simp

/-- The squared truncation error is exactly the sum of the two squared neighbor
excesses.  At most one of the two terms is nonzero, according to `n mod 3`. -/
theorem f3Tail_sq_eq_neighbor_excess (R : ℕ) {n : ℕ} (hn : 1 < n) :
    (f3Tail R n) ^ 2 =
      (v3Excess R (n + 1) : ℤ) ^ 2 + (v3Excess R (n - 1) : ℤ) ^ 2 := by
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · have hl : v3 (n - 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    have hr : v3 (n + 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [f3Tail_of_mod_three_zero hn h0, hl, hr]
    simp [v3Excess]
  · have hr : v3 (n + 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [f3Tail_of_mod_three_one hn h1, hr]
    simp [v3Excess]
  · have hl : v3 (n - 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [f3Tail_of_mod_three_two hn h2, hl]
    simp [v3Excess]

/-- Sum of the first `m` odd positive integers, in the integer coefficient ring. -/
theorem sum_odd_eq_sq_int (m : ℕ) :
    (∑ t ∈ Finset.range m, (2 * (t : ℤ) + 1)) = (m : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The square of one valuation excess is a finite sum of odd layer weights. -/
theorem v3Excess_sq_eq_odd_sum (R n : ℕ) :
    (v3Excess R n : ℤ) ^ 2 =
      ∑ t ∈ Finset.range (v3Excess R n), (2 * (t : ℤ) + 1) := by
  symm
  exact sum_odd_eq_sq_int (v3Excess R n)

/-- Membership in the `t`-th excess layer is exactly divisibility by the corresponding
higher power of three.  The nonzero hypothesis matches mathlib's totalized valuation
convention. -/
theorem pow_three_dvd_iff_lt_v3Excess {R t n : ℕ} (hn : n ≠ 0) :
    3 ^ (R + t + 1) ∣ n ↔ t < v3Excess R n := by
  have hd : 3 ^ (R + t + 1) ∣ n ↔ R + t + 1 ≤ v3 n := by
    rw [v3_eq_padic]
    exact padicValNat_dvd_iff_le hn
  rw [hd]
  unfold v3Excess
  omega

end OmegaBalance
