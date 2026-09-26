import OmegaBalance.F3PadicLogMulDomain

/-!
# Second-order defect for the genuine 3-adic F₃ logarithm

The final multiplicativity theorem is not asserted here.  This module records
the exact algebraic decomposition of its defect into a quadratic displacement
and already-controlled nonlinear logarithm tails.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The exact multiplicativity defect has no first-order term: its algebraic
leading contribution is `Δ(m)Δ(n)`, while the rest consists of nonlinear
logarithm tails. -/
theorem f3PadicLog_mul_defect_eq {m n : ℕ}
    (hm : 1 < m) (hn : 1 < n)
    (hm3 : ¬ 3 ∣ m) (hn3 : ¬ 3 ∣ n) :
    f3PadicLog (m * n) - (f3PadicLog m + f3PadicLog n) =
      f3PadicDelta m * f3PadicDelta n +
        f3PadicLogTail (m * n) -
          f3PadicLogTail m - f3PadicLogTail n := by
  have hn1 : 1 ≤ n := by omega
  have hmn : 1 < m * n := lt_of_lt_of_le hm (by
    simpa using Nat.mul_le_mul_left m hn1)
  have h3mn : ¬ 3 ∣ m * n := f3_three_not_dvd_mul hm3 hn3
  rw [f3PadicLog_eq_delta_add_tail hmn h3mn,
    f3PadicLog_eq_delta_add_tail hm hm3,
    f3PadicLog_eq_delta_add_tail hn hn3,
    f3PadicDelta_mul hm3 hn3]
  ring

end OmegaBalance
