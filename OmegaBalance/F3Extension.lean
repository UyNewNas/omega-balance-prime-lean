import OmegaBalance.F3
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Extending F₃ beyond primes

The existing `f3 : ℕ → ℤ` already has a nonprime domain. This module proves
its arithmetic laws for `n > 1`, and introduces a compatible signed-integer
extension `f3Int`. Values at zero and ±1 retain mathlib's totalization; the
ordinary valuation laws do not silently include those exceptional arguments.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Three-adic valuation of a signed integer, totalized at zero. -/
def v3Int (z : ℤ) : ℕ := padicValInt 3 z

/-- Signed-integer extension; unlike `f3`, subtraction in the argument is in ℤ. -/
def f3Int (z : ℤ) : ℤ := (v3Int (z + 1) : ℤ) - (v3Int (z - 1) : ℤ)

@[simp] theorem v3Int_nat (n : ℕ) : v3Int (n : ℤ) = v3 n := by
  rw [v3Int, padicValInt.of_nat]
  exact (valuation_eq_padicValNat Nat.prime_three n).symm

@[simp] theorem v3Int_neg (z : ℤ) : v3Int (-z) = v3Int z := by
  simp [v3Int, padicValInt]

/-- Compatibility requires n ≥ 1 because the old domain uses truncated subtraction. -/
theorem f3Int_nat {n : ℕ} (hn : 1 ≤ n) : f3Int (n : ℤ) = f3 n := by
  have hp : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by simp
  have hm : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  simp only [f3Int, f3, neighborDiff, hp, hm, v3Int_nat]

/-- Reflection through zero makes the signed-integer extension an odd function. -/
theorem f3Int_neg (z : ℤ) : f3Int (-z) = -f3Int z := by
  have hp : -z + 1 = -(z - 1) := by ring
  have hm : -z - 1 = -(z + 1) := by ring
  simp only [f3Int, hp, hm, v3Int_neg]
  ring

theorem f3Int_neg_nat {n : ℕ} (hn : 1 ≤ n) : f3Int (-(n : ℤ)) = -f3 n := by
  rw [f3Int_neg, f3Int_nat hn]

/-- Multiples of three have two neighbors with zero three-adic valuation. -/
theorem f3_of_mod_three_zero {n : ℕ} (hn : 1 < n) (hm : n % 3 = 0) :
    f3 n = 0 := by
  have hl : v3 (n - 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  have hr : v3 (n + 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  simp [f3, neighborDiff, hl, hr]

/-- No primality assumption is needed for the zero classification. -/
theorem f3_eq_zero_iff_three_dvd {n : ℕ} (hn : 1 < n) :
    f3 n = 0 ↔ 3 ∣ n := by
  constructor
  · intro hz
    by_contra hd
    have hm : n % 3 ≠ 0 := fun h => hd (Nat.dvd_iff_mod_eq_zero.mpr h)
    have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases cases with h | h
    · have := (f3_of_mod_three_one hn h).2
      omega
    · have := (f3_of_mod_three_two hn h).2
      omega
  · intro hd
    exact f3_of_mod_three_zero hn (Nat.mod_eq_zero_of_dvd hd)

theorem f3_ne_zero_of_not_dvd {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n ≠ 0 := fun hz => h3 ((f3_eq_zero_iff_three_dvd hn).mp hz)

/-- Away from multiples of three, exactly one neighbor contributes. -/
theorem f3_abs_eq_neighbor_sum {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    |f3 n| = (v3 (n - 1) : ℤ) + (v3 (n + 1) : ℤ) := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h
  · have hz : v3 (n + 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [(f3_of_mod_three_one hn h).1, hz]
    simp
  · have hz : v3 (n - 1) = 0 := by
      apply v3_eq_zero_of_not_dvd
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [(f3_of_mod_three_two hn h).1, hz]
    simp

/-- The depth is the valuation of n²−1, provided n > 1 and 3 ∤ n. -/
theorem f3_abs_eq_v3_sq_sub_one {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    |f3 n| = (v3 (n ^ 2 - 1) : ℤ) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hsq : n ^ 2 - 1 + 1 = n ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hid : (n - 1) * (n + 1) = n ^ 2 - 1 := by nlinarith
  have hv := v3_mul (a := n - 1) (b := n + 1) (by omega) (by omega)
  rw [hid] at hv
  rw [f3_abs_eq_neighbor_sum hn h3, hv, Nat.cast_add]

/-- Squaring preserves the depth and makes the sign negative. -/
theorem f3_sq {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 (n ^ 2) = -|f3 n| := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hsq : n ^ 2 % 3 = 1 := by
    rcases cases with h | h <;> norm_num [Nat.pow_mod, h]
  rw [(f3_of_mod_three_one (by nlinarith) hsq).1,
    f3_abs_eq_v3_sq_sub_one hn h3]

/-- A convenient finite-residue criterion for an exact valuation of one. -/
theorem v3_eq_one_of_mod_nine {n : ℕ} (hm : n % 9 = 3) : v3 n = 1 := by
  have hn : n ≠ 0 := by omega
  have hp : 0 < v3 n := by
    apply v3_pos_of_dvd hn
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hi : 3 ^ 2 ∣ n ↔ 2 ≤ v3 n := by
    change 3 ^ 2 ∣ n ↔ 2 ≤ valuation 3 n
    rw [valuation_eq_padicValNat Nat.prime_three]
    exact padicValNat_dvd_iff_le hn
  have hnine : ¬ 3 ^ 2 ∣ n := by
    intro h
    have hz := Nat.mod_eq_zero_of_dvd h
    norm_num at hz
    omega
  have := mt hi.mpr hnine
  omega

/-- The cyclotomic factor of n³−1 adds exactly one factor of three. -/
theorem v3_quad_plus_one {n : ℕ} (hm : n % 3 = 1) :
    v3 (n ^ 2 + n + 1) = 1 := by
  apply v3_eq_one_of_mod_nine
  have cases : n % 9 = 1 ∨ n % 9 = 4 ∨ n % 9 = 7 := by omega
  rcases cases with h | h | h <;> norm_num [Nat.add_mod, Nat.pow_mod, h]

/-- The cyclotomic factor of n³+1 adds exactly one factor of three. -/
theorem v3_quad_minus_one {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    v3 (n ^ 2 - n + 1) = 1 := by
  let t := n / 3
  have ht : n = 3 * t + 2 := by dsimp [t]; omega
  have hsub : n ^ 2 - n + n = n ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hid : n ^ 2 - n + 1 = 3 * (3 * t ^ 2 + 3 * t + 1) := by nlinarith [ht]
  have hz : v3 (3 * t ^ 2 + 3 * t + 1) = 0 := by
    apply v3_eq_zero_of_not_dvd
    intro hd
    have hh := Nat.mod_eq_zero_of_dvd hd
    norm_num [Nat.add_mod, Nat.mul_mod] at hh
  have hv : v3 3 = 1 := by simpa using v3_pow_three 1
  rw [hid, v3_mul (by omega) (by omega), hv, hz]

/-- Cubing a residue-1 integer lowers the signed statistic by one. -/
theorem f3_cube_of_mod_three_one {n : ℕ} (hn : 1 < n) (hm : n % 3 = 1) :
    f3 (n ^ 3) = f3 n - 1 := by
  have hn3 : 1 < n ^ 3 := by nlinarith
  have hm3 : n ^ 3 % 3 = 1 := by norm_num [Nat.pow_mod, hm]
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hsub3 : n ^ 3 - 1 + 1 = n ^ 3 := Nat.sub_add_cancel (by omega)
  have hh := congrArg (fun x : ℕ => x * (n ^ 2 + n + 1)) hsub
  have hid : (n - 1) * (n ^ 2 + n + 1) = n ^ 3 - 1 := by nlinarith [hh]
  have hv := v3_mul (a := n - 1) (b := n ^ 2 + n + 1) (by omega) (by omega)
  rw [hid, v3_quad_plus_one hm] at hv
  rw [(f3_of_mod_three_one hn3 hm3).1, (f3_of_mod_three_one hn hm).1, hv]
  push_cast
  ring

/-- Cubing a residue-2 integer raises the signed statistic by one. -/
theorem f3_cube_of_mod_three_two {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3 (n ^ 3) = f3 n + 1 := by
  have hn3 : 1 < n ^ 3 := by nlinarith
  have hm3 : n ^ 3 % 3 = 2 := by norm_num [Nat.pow_mod, hm]
  have hsub : n ^ 2 - n + n = n ^ 2 := Nat.sub_add_cancel (by nlinarith)
  have hh := congrArg (fun x : ℕ => (n + 1) * x) hsub
  have hid : (n + 1) * (n ^ 2 - n + 1) = n ^ 3 + 1 := by nlinarith [hh]
  have hv := v3_mul (a := n + 1) (b := n ^ 2 - n + 1) (by omega) (by omega)
  rw [hid, v3_quad_minus_one hn hm] at hv
  rw [(f3_of_mod_three_two hn3 hm3).1, (f3_of_mod_three_two hn hm).1, hv]
  simp

/-- Equivalent to adding sign(F₃(n)); no primality assumption. -/
theorem f3_cube {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 (n ^ 3) = if 0 < f3 n then f3 n + 1 else f3 n - 1 := by
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have cases : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h
  · rw [if_neg (by have := (f3_of_mod_three_one hn h).2; omega)]
    exact f3_cube_of_mod_three_one hn h
  · rw [if_pos (f3_of_mod_three_two hn h).2]
    exact f3_cube_of_mod_three_two hn h

end OmegaBalance
