import OmegaBalance.F3Arithmetic
import Mathlib.NumberTheory.Multiplicity

/-!
# Arbitrary positive powers of F₃

This uses mathlib's proved lifting-the-exponent theorem, not a new axiom.
The exponent must be nonzero: the ordinary valuation of n^0 - 1 is infinite.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem v3_eq_padic (n : ℕ) : v3 n = padicValNat 3 n :=
  valuation_eq_padicValNat Nat.prime_three n

theorem three_not_dvd_pow {n : ℕ} (h3 : ¬ 3 ∣ n) (e : ℕ) : ¬ 3 ∣ n ^ e := by
  intro h
  exact h3 (Nat.prime_three.dvd_of_dvd_pow h)

/-- LTE at three for a positive natural number congruent to one. -/
theorem v3_pow_sub_one {n e : ℕ} (hn : 1 < n) (hm : n % 3 = 1) (he : e ≠ 0) :
    v3 (n ^ e - 1) = v3 (n - 1) + v3 e := by
  have hd : 3 ∣ n - 1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h3 : ¬ 3 ∣ n := by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    omega
  simp only [v3_eq_padic]
  simpa using padicValNat.pow_sub_pow (p := 3) (x := n) (y := 1)
    (by decide) hn hd h3 he

/-- Every positive power adds precisely v₃(e) to the depth. -/
theorem f3_pow_depth {n e : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) (he : e ≠ 0) :
    |f3 (n ^ e)| = |f3 n| + (v3 e : ℤ) := by
  have hn2 : 1 < n ^ 2 := Nat.one_lt_pow (by decide) hn
  have hnE : 1 < n ^ e := Nat.one_lt_pow he hn
  have hm : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hc : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hs : n ^ 2 % 3 = 1 := by
    rcases hc with h | h <;> norm_num [Nat.pow_mod, h]
  have hv := v3_pow_sub_one hn2 hs he
  have hid : (n ^ e) ^ 2 = (n ^ 2) ^ e := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm e 2]
  rw [f3_abs_eq_v3_sq_sub_one hnE (three_not_dvd_pow h3 e),
    f3_abs_eq_v3_sq_sub_one hn h3, hid, hv, Nat.cast_add]

/-- Residue signs of powers; valid even for exponent zero. -/
theorem f3Side_pow {n : ℕ} (h3 : ¬ 3 ∣ n) (e : ℕ) :
    f3Side (n ^ e) = -(-f3Side n) ^ e := by
  induction e with
  | zero => norm_num [f3Side]
  | succ e ih =>
    rw [pow_succ, f3Side_mul (three_not_dvd_pow h3 e) h3, ih, pow_succ]
    ring

/-- Complete signed positive-power formula, with all subtraction in ℤ. -/
theorem f3_pow {n e : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) (he : e ≠ 0) :
    f3 (n ^ e) = -(-f3Side n) ^ e * (|f3 n| + (v3 e : ℤ)) := by
  rw [f3_eq_side_mul_natAbs (Nat.one_lt_pow he hn) (three_not_dvd_pow h3 e),
    f3Side_pow h3 e]
  have hcast : ((f3 (n ^ e)).natAbs : ℤ) = |f3 (n ^ e)| := Int.natCast_natAbs _
  rw [hcast, f3_pow_depth hn h3 he]

end OmegaBalance
