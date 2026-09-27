import OmegaBalance.F3BFTBManyPrimesAdapter
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace OmegaBalance

/--
Changing an arithmetic-progression main term from `li / d` to `pi / d`
costs at most the global main-term discrepancy divided by the same positive
denominator.
-/
theorem bftb_abs_main_term_change_div
    (x li pi d : ℝ) (hd : 0 < d) :
    |x - pi / d| ≤ |x - li / d| + |li - pi| / d := by
  have hdecomp :
      x - pi / d = (x - li / d) + (li - pi) / d := by
    ring
  rw [hdecomp]
  calc
    |(x - li / d) + (li - pi) / d|
        ≤ |x - li / d| + |(li - pi) / d| := abs_add_le _ _
    _ = |x - li / d| + |li - pi| / d := by
      rw [abs_div, abs_of_pos hd]

/-- Specialize the Li-to-pi normalization inequality to Euler's totient. -/
theorem bftb_abs_main_term_change_totient
    {q : ℕ} (hq : 0 < q) (x li pi : ℝ) :
    |x - pi / (q.totient : ℝ)| ≤
      |x - li / (q.totient : ℝ)| + |li - pi| / (q.totient : ℝ) := by
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast hφnat
  exact bftb_abs_main_term_change_div x li pi (q.totient : ℝ) hφ

/--
For a positive modulus, the denominator `φ(q)` is at least one, so the
normalization cost is at most the global discrepancy `|li - pi|`.
-/
theorem bftb_abs_main_term_change_totient_le
    {q : ℕ} (hq : 0 < q) (x li pi : ℝ) :
    |x - pi / (q.totient : ℝ)| ≤
      |x - li / (q.totient : ℝ)| + |li - pi| := by
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφoneNat : 1 ≤ q.totient := Nat.succ_le_iff.mpr hφnat
  have hφone : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast hφoneNat
  calc
    |x - pi / (q.totient : ℝ)|
        ≤ |x - li / (q.totient : ℝ)| +
            |li - pi| / (q.totient : ℝ) :=
      bftb_abs_main_term_change_totient hq x li pi
    _ ≤ |x - li / (q.totient : ℝ)| + |li - pi| := by
      gcongr
      exact div_le_self (abs_nonneg _) hφone


/--
Summed Li-to-pi normalization while retaining the reciprocal-totient weight.
Keeping this weight is essential: replacing it by one at every modulus would
lose a polynomial factor over a Bombieri--Vinogradov range.
-/
theorem bftb_sum_abs_main_term_change_totient
    (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q)
    (x : ℕ → ℝ) (li pi : ℝ) :
    (∑ q ∈ S, |x q - pi / (q.totient : ℝ)|) ≤
      (∑ q ∈ S, |x q - li / (q.totient : ℝ)|) +
        ∑ q ∈ S, |li - pi| / (q.totient : ℝ) := by
  calc
    (∑ q ∈ S, |x q - pi / (q.totient : ℝ)|)
        ≤ ∑ q ∈ S,
            (|x q - li / (q.totient : ℝ)| +
              |li - pi| / (q.totient : ℝ)) := by
      exact Finset.sum_le_sum fun q hq =>
        bftb_abs_main_term_change_totient (hS q hq) (x q) li pi
    _ = (∑ q ∈ S, |x q - li / (q.totient : ℝ)|) +
          ∑ q ∈ S, |li - pi| / (q.totient : ℝ) := by
      rw [Finset.sum_add_distrib]

/--
Elementary lower bound for Euler's totient:
`q ≤ φ(q) * d(q)`, where `d(q)` is the number of positive divisors.
This is the pointwise input for the reciprocal-totient polylogarithmic ledger.
-/
theorem bftb_le_totient_mul_card_divisors (q : ℕ) :
    q ≤ Nat.totient q * q.divisors.card := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  conv_lhs => rw [← Nat.sum_totient q]
  calc
    q.divisors.sum Nat.totient
        ≤ ∑ d ∈ q.divisors, Nat.totient q :=
      Finset.sum_le_sum fun d hd =>
        Nat.le_of_dvd
          (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = Nat.totient q * q.divisors.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]

/--
For positive `q`, reciprocal totient is bounded by the divisor weight
`d(q)/q`. Summing this will reduce the normalization loss to a standard
divisor-harmonic estimate rather than a polynomial modulus count.
-/
theorem bftb_inv_totient_le_card_divisors_div
    {q : ℕ} (hq : 0 < q) :
    (1 : ℝ) / (q.totient : ℝ) ≤
      (q.divisors.card : ℝ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr hq
  have hφR : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast hφnat
  rw [div_le_div_iff₀ hφR hqR]
  have hreal :
      (q : ℝ) ≤ (q.totient : ℝ) * (q.divisors.card : ℝ) := by
    exact_mod_cast bftb_le_totient_mul_card_divisors q
  simpa [mul_comm] using hreal

end OmegaBalance
