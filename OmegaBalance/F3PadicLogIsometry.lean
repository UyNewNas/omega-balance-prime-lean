import OmegaBalance.F3PadicLogDominant
import Mathlib.Analysis.Normed.Group.Ultra

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

noncomputable def f3PadicLogTail (n : ℕ) : ℚ_[3] :=
  ∑' k : ℕ, f3PadicLogTerm (f3PadicDelta n) (k + 1)

theorem norm_f3PadicLogTerm_delta_le_next_radius {n k : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) (hk : 0 < k) :
    ‖f3PadicLogTerm (f3PadicDelta n) k‖ ≤
      (3 : ℝ) ^ (-((f3PadicDelta n).valuation + 1) : ℤ) := by
  have hx : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  have hden : ((k + 1 : ℕ) : ℚ_[3]) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have ht : f3PadicLogTerm (f3PadicDelta n) k ≠ 0 := by
    unfold f3PadicLogTerm
    rw [show (k : ℚ_[3]) + 1 = ((k + 1 : ℕ) : ℚ_[3]) by norm_num]
    exact div_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hx))
      hden
  rw [Padic.norm_eq_zpow_neg_valuation ht]
  apply (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num)).monotone
  have hv := f3PadicLogTerm_delta_valuation_gt hn h3 hk
  omega

theorem norm_f3PadicLogTail_le_next_radius {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicLogTail n‖ ≤
      (3 : ℝ) ^ (-((f3PadicDelta n).valuation + 1) : ℤ) := by
  unfold f3PadicLogTail
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  exact norm_f3PadicLogTerm_delta_le_next_radius hn h3 (Nat.succ_pos k)

theorem norm_f3PadicLogTail_lt_delta {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicLogTail n‖ < ‖f3PadicDelta n‖ := by
  have hx : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  calc
    ‖f3PadicLogTail n‖
        ≤ (3 : ℝ) ^ (-((f3PadicDelta n).valuation + 1) : ℤ) :=
      norm_f3PadicLogTail_le_next_radius hn h3
    _ < (3 : ℝ) ^ (-(f3PadicDelta n).valuation : ℤ) := by
      exact (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num)) (by omega)
    _ = ‖f3PadicDelta n‖ := by
      symm
      exact Padic.norm_eq_zpow_neg_valuation hx

theorem f3PadicLog_eq_delta_add_tail {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3PadicLog n = f3PadicDelta n + f3PadicLogTail n := by
  unfold f3PadicLog f3PadicLogOnePlus f3PadicLogTail
  have hs := summable_f3PadicLog hn h3
  simpa [f3PadicLogTerm] using (hs.sum_add_tsum_nat_add 1).symm

theorem f3PadicLog_norm_eq_delta_norm {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    ‖f3PadicLog n‖ = ‖f3PadicDelta n‖ := by
  rw [f3PadicLog_eq_delta_add_tail hn h3]
  have htail := norm_f3PadicLogTail_lt_delta hn h3
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt htail)]
  exact max_eq_left htail.le

theorem f3PadicLog_ne_zero {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3PadicLog n ≠ 0 := by
  intro hz
  have hnorm := f3PadicLog_norm_eq_delta_norm hn h3
  rw [hz, norm_zero] at hnorm
  have hx : 0 < ‖f3PadicDelta n‖ := norm_pos_iff.mpr (f3PadicDelta_ne_zero hn)
  linarith

theorem f3PadicLog_valuation {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    (f3PadicLog n).valuation = ((f3 n).natAbs : ℤ) := by
  have hl : f3PadicLog n ≠ 0 := f3PadicLog_ne_zero hn h3
  have hd : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  have hnorm := f3PadicLog_norm_eq_delta_norm hn h3
  rw [Padic.norm_eq_zpow_neg_valuation hl,
    Padic.norm_eq_zpow_neg_valuation hd] at hnorm
  have hneg :
      (-(f3PadicLog n).valuation : ℤ) =
        (-(f3PadicDelta n).valuation : ℤ) :=
    (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num)).injective hnorm
  have hval :
      (f3PadicLog n).valuation = (f3PadicDelta n).valuation := by
    omega
  rw [hval, f3PadicDelta_valuation hn h3]

theorem f3_eq_neg_chi_mul_log_valuation {n : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n = -f3Chi n * (f3PadicLog n).valuation := by
  rw [f3_eq_neg_chi_mul_natAbs hn h3, f3PadicLog_valuation hn h3]

end OmegaBalance
