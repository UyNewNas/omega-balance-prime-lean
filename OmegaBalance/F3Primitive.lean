import OmegaBalance.F3Order
import OmegaBalance.F3SumProduct

/-! Maximal multiplicative orders: F₃ = 1 is the primitive-root criterion. -/
namespace OmegaBalance

/-- Order six modulo nine is equivalent to the exact positive level one. -/
theorem f3_eq_one_iff_order_nine {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n = 1 ↔ orderOf (n : ZMod 9) = 6 := by
  constructor
  · intro hf
    have hm := (f3_positive_level (k := 1) hn (by decide) hf).1
    have h := f3_orderOf_pos (r := 2) hn hm (by decide)
    simpa [hf] using h
  · intro ho
    have hm0 : n % 3 ≠ 0 := fun h => h3 (Nat.dvd_iff_mod_eq_zero.mpr h)
    have hc : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have hd : 0 < (f3 n).natAbs := by
      have hf := f3_ne_zero_of_not_dvd hn h3
      have hne : (f3 n).natAbs ≠ 0 := by
        intro h
        exact hf (Int.natAbs_eq_zero.mp h)
      omega
    rcases hc with hm | hm
    · have hh := f3_orderOf_neg hn hm 2
      norm_num at hh
      rw [ho] at hh
      by_cases he : (f3 n).natAbs = 1
      · norm_num [he] at hh
      · have he' : 2 - (f3 n).natAbs = 0 := by omega
        norm_num [he'] at hh
    · have hh := f3_orderOf_pos (r := 2) hn hm (by decide)
      norm_num at hh
      rw [ho] at hh
      have he : (f3 n).natAbs = 1 := by
        by_contra h
        have he' : 2 - (f3 n).natAbs = 0 := by omega
        norm_num [he'] at hh
      rw [f3_eq_side_mul_natAbs hn h3]
      simp [f3Side, hm, he]

/-- The exact maximal-order criterion simultaneously for all powers of three. -/
theorem f3_eq_one_iff_maximal_order_tower {n : ℕ} (hn : 1 < n) (h3 : ¬ 3 ∣ n) :
    f3 n = 1 ↔ ∀ r : ℕ, 0 < r →
      orderOf (n : ZMod (3 ^ r)) = 2 * 3 ^ (r - 1) := by
  constructor
  · intro hf r hr
    have hm := (f3_positive_level (k := 1) hn (by decide) hf).1
    simpa [hf] using f3_orderOf_pos hn hm hr
  · intro h
    apply (f3_eq_one_iff_order_nine hn h3).mpr
    simpa using h 2 (by decide)

end OmegaBalance
