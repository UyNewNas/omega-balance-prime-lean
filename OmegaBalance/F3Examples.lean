import OmegaBalance.F3Arithmetic
import OmegaBalance.Examples

/-! Regression proofs for the integer extension and its nonprime arithmetic. -/
namespace OmegaBalance

theorem f3Int_negative_five_example : f3Int (-5) = -1 := by
  have h := f3Int_neg_nat (n := 5) (by decide)
  norm_num at h
  exact h

theorem f3_square_five_example : f3 25 = -1 := by
  have h := f3_sq (n := 5) (by decide) (by norm_num)
  norm_num at h
  exact h

theorem f3_cube_five_example : f3 125 = 2 := by
  have h := f3_cube_of_mod_three_two (n := 5) (by decide) (by decide)
  norm_num at h
  exact h

theorem f3_cube_seven_example : f3 343 = -2 := by
  have h := f3_cube_of_mod_three_one (n := 7) (by decide) (by decide)
  norm_num at h
  exact h

/-- The reflection law even works for an odd total, here 2+7=9. -/
theorem f3_reflection_nine_example : f3 7 = -f3 2 := by
  apply f3_reflection (by decide) (by decide) (by norm_num) (by norm_num)
  have hv : v3 (2 + 7) = 2 := by simpa using v3_pow_three 2
  rw [hv]
  norm_num [f3, neighborDiff]

theorem f3_multiply_unequal_example : |f3 (5 * 17)| = 1 := by
  have hv : f3 17 = 2 := twin_seventeen_nineteen_example.1
  have h := (f3_mul_depth (m := 5) (n := 17) (by decide) (by decide)
    (by norm_num) (by norm_num)).2 (by norm_num [hv])
  norm_num [hv] at h
  exact h

theorem f3_iterated_cube_five_example (r : ℕ) :
    f3 (5 ^ (3 ^ r)) = 1 + (r : ℤ) := by
  simpa using (f3_iterated_cube_pos (n := 5) (by decide) (by decide) r).2

/-- Equality at the reflection threshold is insufficient: 30=11+19. -/
theorem f3_reflection_strict_boundary_example :
    (f3 11).natAbs = v3 (11 + 19) ∧ f3 19 ≠ -f3 11 := by
  have h11 : f3 11 = 1 := by
    rw [(f3_of_mod_three_two (n := 11) (by decide) (by decide)).1]
    norm_num
  have h19 : f3 19 = -2 := twin_seventeen_nineteen_example.2
  have hv : v3 (11 + 19) = 1 := v3_eq_one_of_mod_nine (by decide)
  norm_num [h11, h19, hv]

end OmegaBalance
