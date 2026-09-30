import OmegaBalance.F3CorrelationLimitExchange

/-!
# F₃ correlation kernel at power-of-three shifts

This module starts COR-2 by evaluating the already-verified infinite correlation
kernel at the shifts `3^r`.  It is deliberately separate from the later
mean-square Cesàro algebra.
-/

namespace OmegaBalance

open Filter Topology

@[simp] theorem f3PadicKernel_two : f3PadicKernel 2 = 1 := by
  rw [f3PadicKernel, if_neg (by norm_num)]
  rw [v3_eq_zero_of_not_dvd (by norm_num)]
  norm_num

@[simp] theorem f3PadicKernel_one : f3PadicKernel 1 = 1 := by
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
  have hdist : Nat.dist 0 2 = 2 := by decide
  rw [hdist, f3PadicKernel_two, f3PadicKernel_zero]
  norm_num

/-- The shift-one correlation kernel.  This is the separate `r = 0`
boundary case for the power-of-three mean-square family. -/
theorem f3CorrelationKernel_one :
    f3PadicKernel (Nat.dist 1 2) + f3PadicKernel (1 + 2) -
        2 * f3PadicKernel 1 = (-2 / 3 : ℝ) := by
  have hdist : Nat.dist 1 2 = 1 := by decide
  have hthree : f3PadicKernel 3 = (1 / 3 : ℝ) := by
    simpa using (f3PadicKernel_pow_three 1)
  rw [hdist, show 1 + 2 = 3 by norm_num, f3PadicKernel_one, hthree]
  norm_num

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


/-- COR-1 specialized to zero shift: the raw square mean tends to the zero-shift
correlation kernel value `2`. -/
theorem tendsto_f3CorrelationIccAverage_zero :
    Tendsto (fun N : ℕ => f3CorrelationIccAverage 0 N) atTop (𝓝 2) := by
  have hlim := tendsto_f3CorrelationIccAverage 0
  rw [f3CorrelationKernel_zero] at hlim
  exact hlim

/-- COR-1 specialized to shift one.  Its value is `-2/3`, not the
nontrivial power-of-three formula used for `r > 0`. -/
theorem tendsto_f3CorrelationIccAverage_one :
    Tendsto (fun N : ℕ => f3CorrelationIccAverage 1 N) atTop
      (𝓝 (-2 / 3 : ℝ)) := by
  have hlim := tendsto_f3CorrelationIccAverage 1
  rw [f3CorrelationKernel_one] at hlim
  exact hlim

/-- COR-1 specialized to the nontrivial power-of-three shift `3^r`. -/
theorem tendsto_f3CorrelationIccAverage_pow_three {r : ℕ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => f3CorrelationIccAverage (3 ^ r) N) atTop
      (𝓝 (2 - 2 / (3 : ℝ) ^ r)) := by
  have hlim := tendsto_f3CorrelationIccAverage (3 ^ r)
  rw [f3CorrelationKernel_pow_three hr] at hlim
  exact hlim

end OmegaBalance
