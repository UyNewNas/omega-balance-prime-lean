import OmegaBalance.F3PadicLogCompositionTrunc
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

noncomputable def f3PadicNormAbsoluteValue : AbsoluteValue ℚ_[3] ℝ :=
  NormedField.toAbsoluteValue ℚ_[3]

@[simp]
theorem f3PadicNormAbsoluteValue_apply (z : ℚ_[3]) :
    f3PadicNormAbsoluteValue z = ‖z‖ := rfl

theorem f3PadicNormAbsoluteValue_nonarchimedean :
    IsNonarchimedean f3PadicNormAbsoluteValue := by
  intro x y
  exact Padic.nonarchimedean x y

theorem f3PadicLogMulPolynomial_gaussNorm_le_one_third
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ)) :
    (f3PadicLogMulPolynomial x y).gaussNorm f3PadicNormAbsoluteValue 1
      ≤ (1 / 3 : ℝ) := by
  have hna :
      IsNonarchimedean
        (Polynomial.gaussNorm f3PadicNormAbsoluteValue (1 : ℝ)) :=
    Polynomial.isNonarchimedean_gaussNorm
      f3PadicNormAbsoluteValue
      f3PadicNormAbsoluteValue_nonarchimedean (by norm_num)
  have hxterm :
      (Polynomial.C x * Polynomial.X : Polynomial ℚ_[3]).gaussNorm
          f3PadicNormAbsoluteValue 1 = ‖x‖ := by
    rw [show (Polynomial.C x * Polynomial.X : Polynomial ℚ_[3]) =
        Polynomial.monomial 1 x by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one]]
    simp
  have hyterm :
      (Polynomial.C y * Polynomial.X : Polynomial ℚ_[3]).gaussNorm
          f3PadicNormAbsoluteValue 1 = ‖y‖ := by
    rw [show (Polynomial.C y * Polynomial.X : Polynomial ℚ_[3]) =
        Polynomial.monomial 1 y by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one]]
    simp
  have hxyterm :
      (Polynomial.C (x * y) * Polynomial.X ^ 2 : Polynomial ℚ_[3]).gaussNorm
          f3PadicNormAbsoluteValue 1 = ‖x * y‖ := by
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    simp
  calc
    (f3PadicLogMulPolynomial x y).gaussNorm f3PadicNormAbsoluteValue 1
        ≤ max
            ((Polynomial.C x * Polynomial.X + Polynomial.C y * Polynomial.X :
                Polynomial ℚ_[3]).gaussNorm f3PadicNormAbsoluteValue 1)
            ((Polynomial.C (x * y) * Polynomial.X ^ 2 :
                Polynomial ℚ_[3]).gaussNorm f3PadicNormAbsoluteValue 1) := by
          simpa [f3PadicLogMulPolynomial] using
            hna
              (Polynomial.C x * Polynomial.X + Polynomial.C y * Polynomial.X)
              (Polynomial.C (x * y) * Polynomial.X ^ 2)
    _ ≤ max (max ‖x‖ ‖y‖) ‖x * y‖ := by
          apply max_le_max
          · calc
              (Polynomial.C x * Polynomial.X + Polynomial.C y * Polynomial.X :
                  Polynomial ℚ_[3]).gaussNorm f3PadicNormAbsoluteValue 1
                  ≤ max
                    ((Polynomial.C x * Polynomial.X : Polynomial ℚ_[3]).gaussNorm
                      f3PadicNormAbsoluteValue 1)
                    ((Polynomial.C y * Polynomial.X : Polynomial ℚ_[3]).gaussNorm
                      f3PadicNormAbsoluteValue 1) := hna _ _
              _ = max ‖x‖ ‖y‖ := by rw [hxterm, hyterm]
          · rw [hxyterm]
    _ ≤ (1 / 3 : ℝ) := by
          rw [norm_mul]
          apply max_le
          · exact max_le hx hy
          · calc
              ‖x‖ * ‖y‖ ≤ (1 / 3 : ℝ) * (1 / 3 : ℝ) :=
                mul_le_mul hx hy (norm_nonneg _) (by norm_num)
              _ ≤ (1 / 3 : ℝ) := by norm_num

theorem norm_f3PadicLogMulPolynomial_pow_coeff_le
    {x y : ℚ_[3]}
    (hx : ‖x‖ ≤ (1 / 3 : ℝ)) (hy : ‖y‖ ≤ (1 / 3 : ℝ))
    (d n : ℕ) :
    ‖(f3PadicLogMulPolynomial x y ^ d).coeff n‖
      ≤ (1 / 3 : ℝ) ^ d := by
  have hmul :
      ∀ m : ℕ,
        (f3PadicLogMulPolynomial x y ^ m).gaussNorm
            f3PadicNormAbsoluteValue 1 =
          ((f3PadicLogMulPolynomial x y).gaussNorm
            f3PadicNormAbsoluteValue 1) ^ m := by
    intro m
    induction m with
    | zero =>
        simpa using
          (Polynomial.gaussNorm_C
            f3PadicNormAbsoluteValue (1 : ℝ) (1 : ℚ_[3]))
    | succ m ih =>
        rw [pow_succ,
          Polynomial.gaussNorm_mul
            f3PadicNormAbsoluteValue_nonarchimedean
            (by norm_num : (0 : ℝ) < 1),
          ih, pow_succ]
  have hcoeff :=
    Polynomial.le_gaussNorm f3PadicNormAbsoluteValue
      (f3PadicLogMulPolynomial x y ^ d) (by norm_num : (0 : ℝ) ≤ 1) n
  calc
    ‖(f3PadicLogMulPolynomial x y ^ d).coeff n‖
        ≤ (f3PadicLogMulPolynomial x y ^ d).gaussNorm
            f3PadicNormAbsoluteValue 1 := by
          simpa using hcoeff
    _ = ((f3PadicLogMulPolynomial x y).gaussNorm
          f3PadicNormAbsoluteValue 1) ^ d := hmul d
    _ ≤ (1 / 3 : ℝ) ^ d := by
          gcongr
          · exact Polynomial.gaussNorm_nonneg
              f3PadicNormAbsoluteValue
              (f3PadicLogMulPolynomial x y) (by norm_num)
          · exact f3PadicLogMulPolynomial_gaussNorm_le_one_third hx hy

end OmegaBalance
