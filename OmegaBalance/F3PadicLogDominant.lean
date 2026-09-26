import OmegaBalance.F3PadicLog

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- Every F₃ principal-unit displacement lies in the closed radius-1/3 ball. -/
theorem f3PadicDelta_norm_le_one_third {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta n‖ ≤ (3 : ℝ)⁻¹ := by
  have hf : f3 n ≠ 0 := f3_ne_zero_of_not_dvd hn h3
  have hd : 1 ≤ (f3 n).natAbs := Int.natAbs_pos.mpr hf
  rw [f3PadicDelta_norm hn h3]
  have hexp : (-(f3 n).natAbs : ℤ) ≤ (-1 : ℤ) := by
    exact neg_le_neg (by exact_mod_cast hd)
  have hmono :=
    (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num)).monotone hexp
  simpa [zpow_neg_one] using hmono

end OmegaBalance
