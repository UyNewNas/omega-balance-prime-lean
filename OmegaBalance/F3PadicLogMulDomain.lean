import OmegaBalance.F3PadicLogFormal

/-!
# Multiplicative-domain bridge for the genuine 3-adic F₃ logarithm

This module does not assert logarithmic multiplicativity yet.  It closes the
algebraic and convergence-domain reduction needed for that theorem: products
of admissible F₃ inputs remain in the logarithm domain, and the displacement
of a product is exactly `x + y + x*y`.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- If neither input is divisible by three, neither is their product. -/
theorem f3_three_not_dvd_mul {m n : ℕ}
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ¬ 3 ∣ m * n := by
  rw [Nat.prime_three.dvd_mul]
  exact not_or.mpr ⟨hm3, hn3⟩

/-- The principal-unit displacement of a product is the usual multiplicative
formal-group law `x + y + x*y`. -/
theorem f3PadicDelta_mul {m n : ℕ}
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3PadicDelta (m * n) =
      f3PadicDelta m + f3PadicDelta n +
        f3PadicDelta m * f3PadicDelta n := by
  unfold f3PadicDelta
  rw [f3PadicUnit_mul hm3 hn3]
  ring

/-- Equivalently, `1 + Δ` turns multiplication of inputs into multiplication
of principal units. -/
theorem one_add_f3PadicDelta_mul {m n : ℕ}
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    1 + f3PadicDelta (m * n) =
      (1 + f3PadicDelta m) * (1 + f3PadicDelta n) := by
  rw [f3PadicDelta_mul hm3 hn3]
  ring

/-- For admissible inputs the nonlinear product displacement remains inside
the open unit ball, so the genuine logarithm series converges there. -/
theorem f3PadicDelta_mul_norm_lt_one {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    ‖f3PadicDelta m + f3PadicDelta n +
        f3PadicDelta m * f3PadicDelta n‖ < 1 := by
  have hn1 : 1 ≤ n := by omega
  have hmn : 1 < m * n := lt_of_lt_of_le hm (by
    simpa using Nat.mul_le_mul_left m hn1)
  rw [← f3PadicDelta_mul hm3 hn3]
  exact f3PadicDelta_norm_lt_one hmn (f3_three_not_dvd_mul hm3 hn3)

/-- The desired product logarithm is exactly the one-variable logarithm
evaluated at the nonlinear product displacement.  The remaining LOG-1 gap is
therefore the analytic identity `log(1+x+y+xy)=log(1+x)+log(1+y)`. -/
theorem f3PadicLog_mul_reduction {m n : ℕ}
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3PadicLog (m * n) =
      f3PadicLogOnePlus
        (f3PadicDelta m + f3PadicDelta n +
          f3PadicDelta m * f3PadicDelta n) := by
  rw [f3PadicLog, f3PadicDelta_mul hm3 hn3]

/-- The nonlinear product displacement carries the actual convergent
logarithm series whose sum is `f3PadicLog (m*n)`. -/
theorem hasSum_f3PadicLog_mul_delta {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    HasSum
      (fun k : ℕ =>
        f3PadicLogTerm
          (f3PadicDelta m + f3PadicDelta n +
            f3PadicDelta m * f3PadicDelta n) k)
      (f3PadicLog (m * n)) := by
  have hn1 : 1 ≤ n := by omega
  have hmn : 1 < m * n := lt_of_lt_of_le hm (by
    simpa using Nat.mul_le_mul_left m hn1)
  have h :=
    hasSum_f3PadicLog hmn (f3_three_not_dvd_mul hm3 hn3)
  rw [f3PadicDelta_mul hm3 hn3] at h
  exact h

end OmegaBalance
