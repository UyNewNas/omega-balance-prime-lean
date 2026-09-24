import OmegaBalance.F3CorrelationWeight
import Mathlib.Data.Nat.Dist

/-!
# Capped three-adic depths for the finite F₃ correlation

The periodic correlation formula is expressed with congruence predicates.  To
prepare the geometric and limiting steps, this module turns those predicates
into retained three-adic depths while preserving the exceptional zero
convention: at cutoff `R`, zero has depth `R`, not mathlib's totalized
`v3 0 = 0`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Three-adic depth capped at `R`, with zero retaining every finite layer. -/
def f3CappedDepth (R n : ℕ) : ℕ :=
  if n = 0 then R else min R (v3 n)

@[simp] theorem f3CappedDepth_zero (R : ℕ) : f3CappedDepth R 0 = R := by
  simp [f3CappedDepth]

theorem f3CappedDepth_eq_min {n : ℕ} (hn : n ≠ 0) (R : ℕ) :
    f3CappedDepth R n = min R (v3 n) := by
  simp [f3CappedDepth, hn]

/-- The integer-valued finite divisibility expansion is exactly the capped
natural depth, including at zero. -/
theorem v3Trunc_eq_cappedDepth (R n : ℕ) :
    v3Trunc R n = (f3CappedDepth R n : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [v3Trunc_eq_min hn, f3CappedDepth_eq_min hn]

/-- Below the cutoff, divisibility by a power of three is equivalent to lying
below the capped depth. -/
theorem pow_three_dvd_iff_le_f3CappedDepth {m R n : ℕ} (hm : m ≤ R) :
    3 ^ m ∣ n ↔ m ≤ f3CappedDepth R n := by
  by_cases hn : n = 0
  · subst n
    simp [hm]
  · rw [f3CappedDepth_eq_min hn, v3_eq_padic, padicValNat_dvd_iff_le hn]
    omega

/-- Congruence to zero modulo a retained power of three is exactly the capped
depth test. -/
theorem modEq_zero_pow_three_iff_le_f3CappedDepth {m R n : ℕ} (hm : m ≤ R) :
    n ≡ 0 [MOD 3 ^ m] ↔ m ≤ f3CappedDepth R n := by
  rw [Nat.modEq_zero_iff_dvd, pow_three_dvd_iff_le_f3CappedDepth hm]

/-- A congruence to `2` is divisibility of the unsigned distance from `2`.
This single statement covers `h<2`, `h=2`, and `h>2`. -/
theorem modEq_two_iff_dvd_dist (m h : ℕ) :
    h ≡ 2 [MOD m] ↔ m ∣ Nat.dist h 2 := by
  by_cases hh : h ≤ 2
  · rw [Nat.dist_eq_sub_of_le hh, Nat.modEq_iff_dvd' hh]
  · have h2 : 2 ≤ h := by omega
    rw [Nat.dist_eq_sub_of_le_right h2, Nat.ModEq.comm, Nat.modEq_iff_dvd' h2]

/-- The cross-sign compatibility `h ≡ 2` is therefore a capped-depth test on
`dist h 2`. -/
theorem modEq_two_pow_three_iff_le_f3CappedDepth {m R h : ℕ} (hm : m ≤ R) :
    h ≡ 2 [MOD 3 ^ m] ↔ m ≤ f3CappedDepth R (Nat.dist h 2) := by
  rw [modEq_two_iff_dvd_dist, pow_three_dvd_iff_le_f3CappedDepth hm]

/-- Pure finite algebra: a signed sum of three depth-cutoff kernels is exactly
the same signed combination of the generic correlation weights. -/
theorem f3CorrelationThreeWeightSum (R d0 d1 d2 : ℕ) :
    (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
      ((if min (j + 1) (k + 1) ≤ d0 then
          2 * (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) -
        (if min (j + 1) (k + 1) ≤ d1 then
          (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) -
        (if min (j + 1) (k + 1) ≤ d2 then
          (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0))) =
      2 * f3CorrelationWeight R d0 - f3CorrelationWeight R d1 -
        f3CorrelationWeight R d2 := by
  have hscale :
      (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        if min (j + 1) (k + 1) ≤ d0 then
          2 * (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) =
        2 * (∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
          if min (j + 1) (k + 1) ≤ d0 then
            (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
    calc
      _ = ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
          2 * (if min (j + 1) (k + 1) ≤ d0 then
            (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : min (j + 1) (k + 1) ≤ d0 <;> simp [h]
      _ = ∑ j ∈ Finset.range R,
          2 * (∑ k ∈ Finset.range R,
            if min (j + 1) (k + 1) ≤ d0 then
              (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  unfold f3CorrelationWeight
  simp only [Finset.sum_sub_distrib]
  rw [hscale]

/-- The complete finite-period correlation is the signed combination of three
capped-depth weights.  This is still a finite theorem; no limit exchange is
used here. -/
theorem f3PeriodicCorrelationSum_eq_weights (R h : ℕ) :
    f3PeriodicCorrelationSum R h =
      2 * f3CorrelationWeight R (f3CappedDepth R h) -
        f3CorrelationWeight R (f3CappedDepth R (Nat.dist h 2)) -
        f3CorrelationWeight R (f3CappedDepth R (h + 2)) := by
  rw [f3PeriodicCorrelationSum_eq_explicit]
  calc
    _ = ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        ((if min (j + 1) (k + 1) ≤ f3CappedDepth R h then
            2 * (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) -
          (if min (j + 1) (k + 1) ≤ f3CappedDepth R (Nat.dist h 2) then
            (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0) -
          (if min (j + 1) (k + 1) ≤ f3CappedDepth R (h + 2) then
            (3 : ℤ) ^ (R - max (j + 1) (k + 1)) else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjR : j + 1 ≤ R := by
        have := Finset.mem_range.mp hj
        omega
      apply Finset.sum_congr rfl
      intro k hk
      have hkR : k + 1 ≤ R := by
        have := Finset.mem_range.mp hk
        omega
      have hmR : min (j + 1) (k + 1) ≤ R := by omega
      rw [modEq_zero_pow_three_iff_le_f3CappedDepth hmR,
        modEq_two_pow_three_iff_le_f3CappedDepth hmR,
        modEq_zero_pow_three_iff_le_f3CappedDepth hmR]
      norm_cast
    _ = _ := f3CorrelationThreeWeightSum R (f3CappedDepth R h)
      (f3CappedDepth R (Nat.dist h 2)) (f3CappedDepth R (h + 2))

end OmegaBalance
