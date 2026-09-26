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


/-- Exact additive valuation of one logarithm-series term away from zero. -/
theorem f3PadicLogTerm_valuation {x : ℚ_[3]} (hx : x ≠ 0) (k : ℕ) :
    (f3PadicLogTerm x k).valuation =
      ((k + 1 : ℕ) : ℤ) * x.valuation -
        (padicValNat 3 (k + 1) : ℤ) := by
  have hneg : (-1 : ℚ_[3]) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hxpow : x ^ (k + 1) ≠ 0 := pow_ne_zero _ hx
  have hden : ((k + 1 : ℕ) : ℚ_[3]) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  unfold f3PadicLogTerm
  rw [div_eq_mul_inv,
    Padic.valuation_mul (mul_ne_zero hneg hxpow) (inv_ne_zero hden),
    Padic.valuation_mul hneg hxpow,
    Padic.valuation_pow, Padic.valuation_pow,
    Padic.valuation_inv, Padic.valuation_natCast]
  have hminus : ((-1 : ℚ_[3])).valuation = 0 := by
    rw [← Int.cast_neg, Padic.valuation_intCast]
    norm_num [padicValInt]
  rw [hminus]
  push_cast
  ring

/-- On an actual F₃ principal unit, every term after the linear term has
strictly larger 3-adic valuation. -/
theorem f3PadicLogTerm_delta_valuation_gt {n k : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) (hk : 0 < k) :
    (f3PadicDelta n).valuation <
      (f3PadicLogTerm (f3PadicDelta n) k).valuation := by
  have hx : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  rw [f3PadicLogTerm_valuation hx k, f3PadicDelta_valuation hn h3]
  let d : ℕ := (f3 n).natAbs
  let v : ℕ := padicValNat 3 (k + 1)
  have hf : f3 n ≠ 0 := f3_ne_zero_of_not_dvd hn h3
  have hd : 1 ≤ d := by
    dsimp [d]
    exact Int.natAbs_pos.mpr hf
  have hv3 : 3 * v ≤ k + 1 := by
    simpa [v] using (mul_padicValNat_le (p := 3) (n := k + 1))
  have hvlt : v < k := by omega
  have hkz : (0 : ℤ) ≤ (k : ℤ) := by positivity
  have hdz : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hprod : 0 ≤ (k : ℤ) * ((d : ℤ) - 1) :=
    mul_nonneg hkz (sub_nonneg.mpr hdz)
  dsimp [d, v] at *
  push_cast
  nlinarith

/-- Equivalently, every genuinely higher logarithm term has strictly smaller
3-adic norm than the linear displacement. -/
theorem norm_f3PadicLogTerm_delta_lt_first {n k : ℕ}
    (hn : 1 < n) (h3 : ¬ 3 ∣ n) (hk : 0 < k) :
    ‖f3PadicLogTerm (f3PadicDelta n) k‖ < ‖f3PadicDelta n‖ := by
  have hx : f3PadicDelta n ≠ 0 := f3PadicDelta_ne_zero hn
  have hden : ((k + 1 : ℕ) : ℚ_[3]) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have ht : f3PadicLogTerm (f3PadicDelta n) k ≠ 0 := by
    unfold f3PadicLogTerm
    exact div_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hx))
      hden
  rw [Padic.norm_eq_zpow_neg_valuation ht,
    Padic.norm_eq_zpow_neg_valuation hx]
  exact (zpow_right_strictMono₀ (show (1 : ℝ) < 3 by norm_num))
    (neg_lt_neg (f3PadicLogTerm_delta_valuation_gt hn h3 hk))

end OmegaBalance
