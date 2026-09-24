import OmegaBalance.F3Powers
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact multiplicative orders modulo powers of three

The output is mathlib's `orderOf (n : ZMod (3^r))`, not a separately defined
candidate formula. No primality hypothesis on n is needed.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem nat_pow_zmod_eq_one_iff {n : ℕ} (hn : 1 ≤ n) (e M : ℕ) :
    (n : ZMod M) ^ e = 1 ↔ M ∣ n ^ e - 1 := by
  have hle : 1 ≤ n ^ e := Nat.one_le_pow e hn
  calc
    (n : ZMod M) ^ e = 1 ↔ (n : ZMod M) ^ e - 1 = 0 := sub_eq_zero.symm
    _ ↔ ((n ^ e - 1 : ℕ) : ZMod M) = 0 := by
      rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one]
    _ ↔ M ∣ n ^ e - 1 := ZMod.natCast_eq_zero_iff _ _

/-- Negative-side power congruences are equivalent to one divisibility condition. -/
theorem f3_pow_zmod_neg_iff {n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) (r e : ℕ) :
    (n : ZMod (3 ^ r)) ^ e = 1 ↔ 3 ^ (r - (f3 n).natAbs) ∣ e := by
  by_cases he : e = 0
  · simp [he]
  have hnE : 1 < n ^ e := Nat.one_lt_pow he hn
  have hd : (f3 n).natAbs = v3 (n - 1) := by
    rw [(f3_of_mod_three_one hn hm).1]
    simp
  calc
    (n : ZMod (3 ^ r)) ^ e = 1 ↔ 3 ^ r ∣ n ^ e - 1 :=
      nat_pow_zmod_eq_one_iff (by omega) e _
    _ ↔ r ≤ v3 (n ^ e - 1) := by
      simpa only [v3_eq_padic] using (padicValNat_dvd_iff_le (p := 3) (by omega : n ^ e - 1 ≠ 0))
    _ ↔ r ≤ v3 (n - 1) + v3 e := by rw [v3_pow_sub_one hn hm he]
    _ ↔ r - (f3 n).natAbs ≤ v3 e := by omega
    _ ↔ 3 ^ (r - (f3 n).natAbs) ∣ e := by
      simpa only [v3_eq_padic] using (padicValNat_dvd_iff_le (p := 3) he).symm

/-- Valuation of n^e-1 when the power is on the residue-one side. -/
theorem v3_power_sub_one_from_depth {n e : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n)
    (he : e ≠ 0) (hm : n ^ e % 3 = 1) :
    v3 (n ^ e - 1) = (f3 n).natAbs + v3 e := by
  have hh := f3_pow_depth hn h3 he
  rw [(f3_of_mod_three_one (Nat.one_lt_pow he hn) hm).1, abs_neg,
    abs_of_nonneg (Int.natCast_nonneg _), ← Int.natCast_natAbs (f3 n)] at hh
  exact_mod_cast hh

/-- On the positive side an additional even-exponent condition is necessary. -/
theorem f3_pow_zmod_pos_iff {n r : ℕ} (hn : 1 < n) (hm : n % 3 = 2)
    (hr : 0 < r) (e : ℕ) :
    (n : ZMod (3 ^ r)) ^ e = 1 ↔
      e % 2 = 0 ∧ 3 ^ (r - (f3 n).natAbs) ∣ e := by
  by_cases he : e = 0
  · simp [he]
  have hnE : 1 < n ^ e := Nat.one_lt_pow he hn
  have h3 : ¬ 3 ∣ n := by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    omega
  have hsq : n ^ 2 % 3 = 1 := by norm_num [Nat.pow_mod, hm]
  have mod_even : e % 2 = 0 → n ^ e % 3 = 1 := by
    intro h
    have heq : e = 2 * (e / 2) := by omega
    rw [heq, pow_mul]
    simp [Nat.pow_mod, hsq]
  constructor
  · intro h
    have hd := (nat_pow_zmod_eq_one_iff (by omega : 1 ≤ n) e (3 ^ r)).mp h
    have hd3 : 3 ∣ 3 ^ r := dvd_pow_self 3 (Nat.ne_of_gt hr)
    have hd' := Nat.dvd_trans hd3 hd
    have hmod : n ^ e % 3 = 1 := by
      have := Nat.mod_eq_zero_of_dvd hd'
      omega
    have hEven : e % 2 = 0 := by
      by_contra hE
      have heq : e = 2 * (e / 2) + 1 := by omega
      rw [heq, pow_add, pow_mul] at hmod
      norm_num [Nat.mul_mod, Nat.pow_mod, hsq, hm] at hmod
    have hv : r ≤ v3 (n ^ e - 1) := by
      simpa only [v3_eq_padic] using
        (padicValNat_dvd_iff_le (p := 3) (by omega : n ^ e - 1 ≠ 0)).mp hd
    rw [v3_power_sub_one_from_depth hn h3 he hmod] at hv
    refine ⟨hEven, ?_⟩
    apply (padicValNat_dvd_iff_le (p := 3) he).mpr
    rw [← v3_eq_padic]
    omega
  · rintro ⟨hEven, hd⟩
    have hv : r - (f3 n).natAbs ≤ v3 e := by
      simpa only [v3_eq_padic] using (padicValNat_dvd_iff_le (p := 3) he).mp hd
    apply (nat_pow_zmod_eq_one_iff (by omega : 1 ≤ n) e (3 ^ r)).mpr
    apply (padicValNat_dvd_iff_le (p := 3) (by omega : n ^ e - 1 ≠ 0)).mpr
    rw [← v3_eq_padic, v3_power_sub_one_from_depth hn h3 he (mod_even hEven)]
    omega

/-- Exact order on the residue-one (negative F₃) side. -/
theorem f3_orderOf_neg {n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) (r : ℕ) :
    orderOf (n : ZMod (3 ^ r)) = 3 ^ (r - (f3 n).natAbs) := by
  apply (orderOf_eq_iff (pow_pos (by decide : 0 < (3 : ℕ)) _)).mpr
  constructor
  · exact (f3_pow_zmod_neg_iff hn hm r _).mpr dvd_rfl
  · intro e hlt hpos heq
    have hd := (f3_pow_zmod_neg_iff hn hm r e).mp heq
    exact (not_le.mpr hlt) (Nat.le_of_dvd hpos hd)

/-- Exact order on the residue-two (positive F₃) side. -/
theorem f3_orderOf_pos {n r : ℕ} (hn : 1 < n) (hm : n % 3 = 2) (hr : 0 < r) :
    orderOf (n : ZMod (3 ^ r)) = 2 * 3 ^ (r - (f3 n).natAbs) := by
  have hc : 0 < 3 ^ (r - (f3 n).natAbs) := pow_pos (by decide) _
  apply (orderOf_eq_iff (by omega : 0 < 2 * 3 ^ (r - (f3 n).natAbs))).mpr
  constructor
  · apply (f3_pow_zmod_pos_iff hn hm hr _).mpr
    refine ⟨by simp [Nat.mul_mod], ?_⟩
    exact ⟨2, by ring⟩
  · intro e hlt hpos heq
    obtain ⟨heven, hd⟩ := (f3_pow_zmod_pos_iff hn hm hr e).mp heq
    obtain ⟨t, ht⟩ := hd
    have ht0 : 0 < t := by
      by_contra h
      have hz : t = 0 := by omega
      simp [hz] at ht
      omega
    have hteven : t % 2 = 0 := by
      rw [ht, Nat.mul_mod] at heven
      norm_num [Nat.pow_mod] at heven
      exact heven
    have ht2 : 2 ≤ t := by omega
    nlinarith [ht]

/-- One formula for the entire order tower of every positive three-adic unit. -/
theorem f3_orderOf {n r : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) (hr : 0 < r) :
    orderOf (n : ZMod (3 ^ r)) =
      (if n % 3 = 1 then 1 else 2) * 3 ^ (r - (f3 n).natAbs) := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hc : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hc with h | h
  · simp [h, f3_orderOf_neg hn h r]
  · simp [h, f3_orderOf_pos hn h hr]

/-- Nonexceptional twins have an exact factor-two order relation at every level. -/
theorem f3_twin_orderOf {p r : ℕ} (hp : p.Prime) (hq : (p + 2).Prime)
    (h3 : 3 < p) (hr : 0 < r) :
    orderOf (p : ZMod (3 ^ r)) = 2 * orderOf ((p + 2 : ℕ) : ZMod (3 ^ r)) := by
  obtain ⟨hl, hu⟩ := twin_mod_three hp hq h3
  rw [f3_orderOf_pos (by omega) hl hr, f3_orderOf_neg (by omega) hu r,
    f3_twin_natAbs_eq hp hq h3]

end OmegaBalance
