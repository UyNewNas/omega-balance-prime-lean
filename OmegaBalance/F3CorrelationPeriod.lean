import OmegaBalance.F3CorrelationLayer
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Complete-period expansion for the truncated F₃ correlation

`f3Trunc` uses natural subtraction, so its value at the small boundary points
is not literally a cyclic residue-class function. This module introduces the
corresponding periodic residue-layer truncation, proves that it agrees with
`f3Trunc` on the intended domain `n > 1`, and expands one complete `3^R`
period of its correlation into the exact signed layer kernel.

No infinite Cesàro limit or tail interchange is asserted here.
-/

namespace OmegaBalance

/-- Indicator of one residue class modulo `3^j`, valued in `ℤ`. -/
def f3ModIndicator (j a n : ℕ) : ℤ :=
  if n ≡ a [MOD 3 ^ j] then 1 else 0

/-- The signed `j`-th residue layer: `-1` residue for the `n+1` valuation and
`+1` residue for the `n-1` valuation. -/
def f3ResidueLayer (j n : ℕ) : ℤ :=
  f3ModIndicator j (3 ^ j - 1) n - f3ModIndicator j 1 n

/-- Periodic version of the retained F₃ layers. The exponents are `1,…,R`. -/
def f3PeriodicTrunc (R n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range R, f3ResidueLayer (j + 1) n

/-- The `-1` residue class modulo a power of three is exactly divisibility of
`n+1` by that power. -/
theorem modEq_pow_three_sub_one_iff_dvd_add_one {j n : ℕ} :
    n ≡ 3 ^ j - 1 [MOD 3 ^ j] ↔ 3 ^ j ∣ n + 1 := by
  have hp : 0 < (3 : ℕ) ^ j := pow_pos (by decide) j
  have hsub : 3 ^ j - 1 + 1 = (3 : ℕ) ^ j := Nat.sub_add_cancel (by omega)
  have hzero : (3 : ℕ) ^ j ≡ 0 [MOD 3 ^ j] :=
    (dvd_rfl : (3 : ℕ) ^ j ∣ 3 ^ j).modEq_zero_nat
  constructor
  · intro h
    have hadd := h.add_right 1
    rw [hsub] at hadd
    exact Nat.modEq_zero_iff_dvd.mp (hadd.trans hzero)
  · intro hd
    have hnzero : n + 1 ≡ 0 [MOD 3 ^ j] := hd.modEq_zero_nat
    have hadd : n + 1 ≡ 3 ^ j - 1 + 1 [MOD 3 ^ j] := by
      rw [hsub]
      exact hnzero.trans hzero.symm
    exact hadd.add_right_cancel' 1

/-- Away from the natural-subtraction boundary, the `+1` residue class is
exactly divisibility of `n-1`. -/
theorem modEq_one_iff_dvd_sub_one {j n : ℕ} (hn : 1 ≤ n) :
    n ≡ 1 [MOD 3 ^ j] ↔ 3 ^ j ∣ n - 1 := by
  constructor
  · intro h
    exact (Nat.modEq_iff_dvd' hn).mp h.symm
  · intro hd
    exact ((Nat.modEq_iff_dvd' hn).mpr hd).symm

/-- On the domain used by the original F₃ function, the cyclic residue-layer
truncation is exactly the earlier divisibility truncation. -/
theorem f3PeriodicTrunc_eq_f3Trunc {R n : ℕ} (hn : 1 < n) :
    f3PeriodicTrunc R n = f3Trunc R n := by
  unfold f3PeriodicTrunc f3ResidueLayer f3ModIndicator f3Trunc v3Trunc
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [modEq_pow_three_sub_one_iff_dvd_add_one]
  · apply Finset.sum_congr rfl
    intro j _
    rw [modEq_one_iff_dvd_sub_one (j := j + 1) (n := n) (by omega)]

/-- Summing a product of two residue indicators over a complete period is the
translated overlap count from `F3CorrelationFinite`. -/
theorem sum_f3ModIndicator_mul_shift (R j k a b h : ℕ) :
    (∑ n ∈ Finset.range (3 ^ R),
        f3ModIndicator j a n * f3ModIndicator k b (n + h)) =
      (modShiftPairCount R j k a b h : ℤ) := by
  classical
  unfold f3ModIndicator modShiftPairCount
  calc
    _ = ∑ n ∈ Finset.range (3 ^ R),
        if (n ≡ a [MOD 3 ^ j] ∧ n + h ≡ b [MOD 3 ^ k]) then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro n _
          by_cases ha : n ≡ a [MOD 3 ^ j]
          · by_cases hb : n + h ≡ b [MOD 3 ^ k] <;> simp [ha, hb]
          · simp [ha]
    _ = (((Finset.range (3 ^ R)).filter fun n =>
          n ≡ a [MOD 3 ^ j] ∧ n + h ≡ b [MOD 3 ^ k]).card : ℤ) := by
          simpa using
            (Finset.sum_boole (R := ℤ)
              (fun n : ℕ => n ≡ a [MOD 3 ^ j] ∧ n + h ≡ b [MOD 3 ^ k])
              (Finset.range (3 ^ R)))
    _ = _ := rfl

/-- One pair of signed residue layers sums to the exact four-term layer
correlation count. -/
theorem sum_f3ResidueLayer_mul_shift (R j k h : ℕ) :
    (∑ n ∈ Finset.range (3 ^ R),
        f3ResidueLayer j n * f3ResidueLayer k (n + h)) =
      f3LayerCorrelation R j k h := by
  unfold f3ResidueLayer
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  rw [sum_f3ModIndicator_mul_shift R j k (3 ^ j - 1) (3 ^ k - 1) h,
    sum_f3ModIndicator_mul_shift R j k (3 ^ j - 1) 1 h,
    sum_f3ModIndicator_mul_shift R j k 1 (3 ^ k - 1) h,
    sum_f3ModIndicator_mul_shift R j k 1 1 h]
  unfold f3LayerCorrelation
  ring

/-- Complete-period correlation of the periodic retained layers. -/
def f3PeriodicCorrelationSum (R h : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (3 ^ R), f3PeriodicTrunc R n * f3PeriodicTrunc R (n + h)

/-- Exact finite double-sum expansion of one complete `3^R` period. -/
theorem f3PeriodicCorrelationSum_eq_layer_sum (R h : ℕ) :
    f3PeriodicCorrelationSum R h =
      ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        f3LayerCorrelation R (j + 1) (k + 1) h := by
  unfold f3PeriodicCorrelationSum f3PeriodicTrunc
  calc
    _ = ∑ n ∈ Finset.range (3 ^ R),
        ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
          f3ResidueLayer (j + 1) n * f3ResidueLayer (k + 1) (n + h) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range R, ∑ n ∈ Finset.range (3 ^ R),
        ∑ k ∈ Finset.range R,
          f3ResidueLayer (j + 1) n * f3ResidueLayer (k + 1) (n + h) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        ∑ n ∈ Finset.range (3 ^ R),
          f3ResidueLayer (j + 1) n * f3ResidueLayer (k + 1) (n + h) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          exact sum_f3ResidueLayer_mul_shift R (j + 1) (k + 1) h

/-- The same complete-period correlation with every layer count replaced by
its explicit power-of-three compatibility formula. This is the finite formula
that the subsequent geometric-sum step will simplify. -/
theorem f3PeriodicCorrelationSum_eq_explicit (R h : ℕ) :
    f3PeriodicCorrelationSum R h =
      ∑ j ∈ Finset.range R, ∑ k ∈ Finset.range R,
        ((if h ≡ 0 [MOD 3 ^ min (j + 1) (k + 1)] then
            2 * ((3 ^ (R - max (j + 1) (k + 1)) : ℕ) : ℤ) else 0) -
          (if h ≡ 2 [MOD 3 ^ min (j + 1) (k + 1)] then
            ((3 ^ (R - max (j + 1) (k + 1)) : ℕ) : ℤ) else 0) -
          (if h + 2 ≡ 0 [MOD 3 ^ min (j + 1) (k + 1)] then
            ((3 ^ (R - max (j + 1) (k + 1)) : ℕ) : ℤ) else 0)) := by
  rw [f3PeriodicCorrelationSum_eq_layer_sum]
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
  exact f3LayerCorrelation_eq hjR hkR

end OmegaBalance
