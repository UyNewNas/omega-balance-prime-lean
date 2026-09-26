import OmegaBalance.F3CorrelationLimitExchange

/-!
# F₃ correlation kernel at power-of-three shifts

This module starts COR-2 by evaluating the already-verified infinite correlation
kernel at the shifts `3^r`.  It is deliberately separate from the later
mean-square Cesàro algebra.
-/

namespace OmegaBalance

@[simp] theorem f3PadicKernel_two : f3PadicKernel 2 = 1 := by
  rw [f3PadicKernel, if_neg (by norm_num)]
  rw [v3_eq_zero_of_not_dvd (by norm_num)]
  norm_num

@[simp] theorem f3PadicKernel_pow_three (r : ℕ) :
    f3PadicKernel (3 ^ r) = 1 / (3 : ℝ) ^ r := by
  rw [f3PadicKernel, if_neg (by positivity), v3_pow_three]

theorem f3PadicKernel_pow_three_add_two {r : ℕ} (hr : 0 < r) :
    f3PadicKernel (3 ^ r + 2) = 1 := by
  have hnot : ¬ 3 ∣ 3 ^ r + 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_succ]
  rw [f3PadicKernel, if_neg (by positivity), v3_eq_zero_of_not_dvd hnot]
  norm_num

theorem f3PadicKernel_dist_pow_three_two {r : ℕ} (hr : 0 < r) :
    f3PadicKernel (Nat.dist (3 ^ r) 2) = 1 := by
  have hnot : ¬ 3 ∣ Nat.dist (3 ^ r) 2 := by
    intro hd
    have hm : 3 ^ r ≡ 2 [MOD 3] :=
      (modEq_two_iff_dvd_dist 3 (3 ^ r)).2 hd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simpa [Nat.ModEq, pow_succ] using hm
  have hne : Nat.dist (3 ^ r) 2 ≠ 0 := by
    intro hz
    apply hnot
    simp [hz]
  rw [f3PadicKernel, if_neg hne, v3_eq_zero_of_not_dvd hnot]
  norm_num

/-- Exact value of the limiting correlation kernel at a nontrivial
power-of-three shift. -/
theorem f3CorrelationKernel_pow_three {r : ℕ} (hr : 0 < r) :
    f3PadicKernel (Nat.dist (3 ^ r) 2) +
        f3PadicKernel (3 ^ r + 2) -
        2 * f3PadicKernel (3 ^ r) =
      2 - 2 / (3 : ℝ) ^ r := by
  rw [f3PadicKernel_dist_pow_three_two hr,
    f3PadicKernel_pow_three_add_two hr, f3PadicKernel_pow_three]
  ring

/-- The zero-shift kernel equals two. -/
theorem f3CorrelationKernel_zero :
    f3PadicKernel (Nat.dist 0 2) + f3PadicKernel (0 + 2) -
        2 * f3PadicKernel 0 = 2 := by
  norm_num [f3PadicKernel_zero]

/-- The kernel difference which drives the mean-square `3^r` approximate
period has the target value `4 / 3^r`. -/
theorem f3CorrelationKernel_meanSquare_pow_three {r : ℕ} (hr : 0 < r) :
    2 * (f3PadicKernel (Nat.dist 0 2) + f3PadicKernel (0 + 2) -
          2 * f3PadicKernel 0) -
      2 * (f3PadicKernel (Nat.dist (3 ^ r) 2) +
          f3PadicKernel (3 ^ r + 2) -
          2 * f3PadicKernel (3 ^ r)) =
      4 / (3 : ℝ) ^ r := by
  rw [f3CorrelationKernel_zero, f3CorrelationKernel_pow_three hr]
  ring

end OmegaBalance
