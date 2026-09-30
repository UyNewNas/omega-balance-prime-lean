import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The strict short-window discriminant bound for F3-WAV

This proves only the nondivisibility step of F3-WAV-1-PROOF-BOUND.
The product `(h - 2) * (h + 2)` need not be smaller than the modulus.
Neither conditional transfer nor the later wavelet results are proved here.
-/

namespace OmegaBalance

/-- In the original strict short-shift window, the lower ternary layer does
not divide the discriminant. The `r ≥ 2` paper hypothesis is retained explicitly. -/
theorem f3Wavelet_discriminant_not_dvd {r : ℕ} {h : ℤ} (_hr : 2 ≤ r)
    (hh : 2 < h) (hwindow : h < (3 : ℤ) ^ (2 * r - 1) - 2) :
    ¬ (3 : ℤ) ^ (2 * r - 1) ∣ h ^ 2 - 4 := by
  intro hd
  have hfactor : h ^ 2 - 4 = (h - 2) * (h + 2) := by ring
  have hprod : (3 : ℤ) ^ (2 * r - 1) ∣ (h - 2) * (h + 2) := by
    rwa [← hfactor]
  by_cases hlo : (3 : ℤ) ∣ h - 2
  · have hhi : ¬ (3 : ℤ) ∣ h + 2 := by
      intro hhi
      have hfour : (3 : ℤ) ∣ 4 := by
        convert Int.dvd_sub hhi hlo using 1 <;> ring
      norm_num at hfour
    have hpow := Int.prime_three.pow_dvd_of_dvd_mul_right (2 * r - 1) hhi hprod
    have hle := Int.le_of_dvd (show 0 < h - 2 by omega) hpow
    omega
  · have hpow := Int.prime_three.pow_dvd_of_dvd_mul_left (2 * r - 1) hlo hprod
    have hle := Int.le_of_dvd (show 0 < h + 2 by omega) hpow
    omega

end OmegaBalance
