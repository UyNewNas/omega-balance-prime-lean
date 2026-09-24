import OmegaBalance
import OmegaBalance.Examples

/-! Kernel regression proofs for deeper results and failed converses. -/
namespace OmegaBalance

@[simp] theorem f3_eleven : f3 11 = 1 := by
  have h := (f3_of_mod_three_two (n := 11) (by decide) (by decide)).1
  simpa using h

@[simp] theorem f3_thirty_five : f3 35 = 2 := by
  have hv : v3 36 = 2 := by
    change v3 (4 * 3 ^ 2) = 2
    rw [v3_mul (by decide) (by decide), v3_four, v3_pow_three]
  rw [(f3_of_mod_three_two (n := 35) (by decide) (by decide)).1, hv]
  norm_num

@[simp] theorem f3_seventy_seven : f3 77 = 1 := by
  have hv : v3 78 = 1 := by
    change v3 (26 * 3) = 1
    rw [v3_mul (by decide) (by decide), v3_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 26),
      v3_three]
  rw [(f3_of_mod_three_two (n := 77) (by decide) (by decide)).1, hv]
  norm_num

/-- Prime inputs already refute every proposed scalar multiplication rule. -/
theorem f3_no_scalar_mul_rule :
    ¬ ∃ H : ℤ → ℤ → ℤ, ∀ m n : ℕ,
      m.Prime → n.Prime → 3 < m → 3 < n → f3 (m * n) = H (f3 m) (f3 n) := by
  rintro ⟨H, h⟩
  have h1 := h 5 7 (by decide) (by decide) (by decide) (by decide)
  have h2 := h 11 7 (by decide) (by decide) (by decide) (by decide)
  norm_num at h1 h2
  omega

theorem f3_general_power_example : f3 (5 ^ 12) = -2 := by
  have hv : v3 12 = 1 := v3_twelve
  rw [f3_pow (by decide) (by decide) (by decide), f3_five, hv]
  norm_num [f3Side]

theorem f3_order_five_example : orderOf (5 : ZMod 81) = 54 := by
  have h := f3_orderOf_pos (n := 5) (r := 4) (by decide) (by decide) (by decide)
  norm_num at h
  exact h

theorem f3_twin_order_example (r : ℕ) (hr : 0 < r) :
    orderOf (17 : ZMod (3 ^ r)) = 2 * orderOf (19 : ZMod (3 ^ r)) := by
  exact f3_twin_orderOf (p := 17) (by decide) (by decide) (by decide) hr

theorem f3_primitive_five_example (r : ℕ) (hr : 0 < r) :
    orderOf (5 : ZMod (3 ^ r)) = 2 * 3 ^ (r - 1) :=
  (f3_eq_one_iff_maximal_order_tower (n := 5) (by decide) (by decide)).mp f3_five r hr

@[simp] theorem f3_one_eighty_one : f3 181 = -2 := by
  have hv : v3 180 = 2 := by
    change v3 (20 * 3 ^ 2) = 2
    rw [v3_mul (by decide) (by decide), v3_twenty, v3_pow_three]
  rw [(f3_of_mod_three_one (n := 181) (by decide) (by decide)).1, hv]
  norm_num

/-- Equality at the refined threshold does not imply twin primes. -/
theorem f3_refined_gap_boundary_example :
    Nat.Prime 17 ∧ Nat.Prime 181 ∧ f3 17 = 2 ∧ f3 181 = -2 ∧
    f3 (17 * 181) = 4 ∧ 181 - 17 = 2 + 2 * 3 ^ (2 * 2) := by
  have hp := twin_seventeen_nineteen_example.1
  have hv : v3 3078 = 4 := by
    change v3 (38 * 3 ^ 4) = 4
    rw [v3_mul (by decide) (by decide),
      v3_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 38), v3_pow_three]
  have hm : f3 (17 * 181) = 4 := by
    rw [(f3_of_mod_three_two (n := 17 * 181) (by norm_num) (by norm_num)).1]
    norm_num [hv]
  exact ⟨by norm_num, by norm_num, hp, f3_one_eighty_one, hm, by norm_num⟩

theorem f3_sum_product_branch_example :
    v3 (17 + 19) = 2 ∧ 2 < v3 (17 * 19 + 1) := by
  have h := f3_opposite_sum_product (p := 17) (q := 19) (k := 2)
    (by decide) (by decide) (by decide) twin_seventeen_nineteen_example.1
    twin_seventeen_nineteen_example.2
  have hv : v3 (17 + 19) = 2 := by
    change v3 (4 * 3 ^ 2) = 2
    rw [v3_mul (by decide) (by decide), v3_four, v3_pow_three]
  rcases h with h | h
  · exact h
  · omega

theorem f3_star_rational_example : f3Rat (13 / 5 : ℚ) = 2 := by
  have h := f3Rat_star_of_gt_one (x := 5) (y := 5) (by norm_num) (by norm_num)
  have hs : f3Star 5 5 = (13 / 5 : ℚ) := by norm_num [f3Star]
  have hf : f3Rat 5 = 1 := by simpa using (f3Rat_nat (n := 5) (by decide)).trans f3_five
  rw [hs, hf] at h
  norm_num at h
  exact h

theorem f3_star_integer_example : f3Star 17 19 = 9 ∧ f3Rat 9 = 0 := by
  constructor
  · norm_num [f3Star]
  · have hf : f3 9 = 0 := f3_of_mod_three_zero (by decide) (by decide)
    simpa using (f3Rat_nat (n := 9) (by decide)).trans hf

/-- The truncated divisibility count has a different zero convention. -/
theorem f3_cutoff_zero_boundary : v3Trunc 4 0 = 4 ∧ v3 0 = 0 := by simp

theorem f3_telescoping_example : (∑ i ∈ Finset.range 8, f3 (i + 2)) = 2 := by
  rw [f3_sum_range]
  have h9 : v3 9 = 2 := by simpa using v3_pow_three 2
  have h10 : v3 10 = 0 := v3_eq_zero_of_not_dvd (by decide)
  norm_num [h9, h10]

end OmegaBalance
