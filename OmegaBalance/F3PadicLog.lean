import OmegaBalance.F3PadicLogDomain
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

noncomputable def f3PadicLogTerm (x : ℚ_[3]) (k : ℕ) : ℚ_[3] :=
  (-1 : ℚ_[3]) ^ k * x ^ (k + 1) / (k + 1)

theorem f3Padic_norm_inv_natCast_le (n : ℕ) (hn : 0 < n) :
    ‖((n : ℚ_[3])⁻¹)‖ ≤ (n : ℝ) := by
  have hn0 : (n : ℚ_[3]) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [Padic.norm_eq_zpow_neg_valuation (inv_ne_zero hn0),
    Padic.valuation_inv, Padic.valuation_natCast]
  simp only [neg_neg]
  rw [zpow_natCast]
  exact_mod_cast Nat.le_of_dvd hn pow_padicValNat_dvd

theorem norm_f3PadicLogTerm_le (x : ℚ_[3]) (k : ℕ) :
    ‖f3PadicLogTerm x k‖ ≤
      ((k + 1 : ℕ) : ℝ) * ‖x‖ ^ (k + 1) := by
  rw [f3PadicLogTerm, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  have hden :
      ‖((↑k + 1 : ℚ_[3])⁻¹)‖ ≤ (k : ℝ) + 1 := by
    simpa using f3Padic_norm_inv_natCast_le (k + 1) (Nat.succ_pos k)
  calc
    ‖x‖ ^ (k + 1) * ‖((↑k + 1 : ℚ_[3])⁻¹)‖
        ≤ ‖x‖ ^ (k + 1) * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hden (pow_nonneg (norm_nonneg x) _)
    _ = ((k + 1 : ℕ) : ℝ) * ‖x‖ ^ (k + 1) := by
      push_cast
      ring

theorem tendsto_succ_mul_pow_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto
      (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r ^ (k + 1))
      Filter.atTop (nhds 0) := by
  have hself :
      Filter.Tendsto (fun k : ℕ => (k : ℝ) * r ^ k) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hpow :
      Filter.Tendsto (fun k : ℕ => r ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hsum :
      Filter.Tendsto (fun k : ℕ => (k : ℝ) * r ^ k + r ^ k)
        Filter.atTop (nhds 0) := by
    simpa using hself.add hpow
  have hmul :
      Filter.Tendsto
        (fun k : ℕ => ((k : ℝ) * r ^ k + r ^ k) * r)
        Filter.atTop (nhds 0) := by
    simpa using hsum.mul_const r
  convert hmul using 1
  funext k
  push_cast
  rw [pow_succ]
  ring

theorem tendsto_f3PadicLogTerm_zero {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    Filter.Tendsto (fun k : ℕ => f3PadicLogTerm x k)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm'
    (Filter.Eventually.of_forall fun k => norm_f3PadicLogTerm_le x k)
  exact tendsto_succ_mul_pow_zero (norm_nonneg x) hx

theorem summable_f3PadicLogTerm {x : ℚ_[3]} (hx : ‖x‖ < 1) :
    Summable (fun k : ℕ => f3PadicLogTerm x k) := by
  let r : ℝ := ‖x‖
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact norm_nonneg x
  have hr1 : r < 1 := by
    simpa [r] using hx
  have hrnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hself : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm)
  have hpow : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_lt_one hr0 hr1
  have hmajor :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r ^ (k + 1)) := by
    have h := (hself.add hpow).mul_right r
    convert h using 1
    funext k
    push_cast
    rw [pow_succ]
    ring
  have hnorm : Summable (fun k : ℕ => ‖f3PadicLogTerm x k‖) := by
    refine hmajor.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    simpa [r] using norm_f3PadicLogTerm_le x k
  exact hnorm.of_norm

noncomputable def f3PadicLogOnePlus (x : ℚ_[3]) : ℚ_[3] :=
  ∑' k : ℕ, f3PadicLogTerm x k

noncomputable def f3PadicLog (n : ℕ) : ℚ_[3] :=
  f3PadicLogOnePlus (f3PadicDelta n)

theorem summable_f3PadicLog {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    Summable (fun k : ℕ => f3PadicLogTerm (f3PadicDelta n) k) :=
  summable_f3PadicLogTerm (f3PadicDelta_norm_lt_one hn h3)

theorem hasSum_f3PadicLog {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    HasSum (fun k : ℕ => f3PadicLogTerm (f3PadicDelta n) k)
      (f3PadicLog n) := by
  exact (summable_f3PadicLog hn h3).hasSum

end OmegaBalance
