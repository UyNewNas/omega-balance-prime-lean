import OmegaBalance.F3BFTBBVQOne
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OmegaBalance

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Finite real harmonic factor on the modulus interval `1, ..., R`.
Adapted from Liu--Wang `DirectConductorWeight.lean` at
`b57b7307810c37267e47110d8b5f920e3e681c81`. -/
def bftbHarmonicFactor (R : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 R, (e : ℝ)⁻¹

theorem bftbHarmonicFactor_nonneg (R : ℕ) :
    0 ≤ bftbHarmonicFactor R := by
  unfold bftbHarmonicFactor
  positivity

theorem bftbHarmonicFactor_eq_harmonic (R : ℕ) :
    bftbHarmonicFactor R = (harmonic R : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp [bftbHarmonicFactor]

theorem bftbHarmonicFactor_le_one_add_log (R : ℕ) :
    bftbHarmonicFactor R ≤ 1 + Real.log R := by
  rw [bftbHarmonicFactor_eq_harmonic]
  simpa using harmonic_le_one_add_log R

theorem bftb_sum_inv_multiples_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0) =
      (e : ℝ)⁻¹ * bftbHarmonicFactor (R / e) := by
  rw [← Finset.sum_filter]
  symm
  rw [bftbHarmonicFactor, Finset.mul_sum]
  refine Finset.sum_bij (fun k _ => e * k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    exact ⟨⟨Nat.mul_pos he hk.1,
      (Nat.mul_le_mul_left e hk.2).trans (Nat.mul_div_le R e)⟩,
      dvd_mul_right e k⟩
  · intro k₁ hk₁ k₂ hk₂ h
    exact Nat.eq_of_mul_eq_mul_left he h
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    refine ⟨r / e, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd hr.1.1 hr.2) he,
        Nat.div_le_div_right hr.1.2⟩
    · exact Nat.mul_div_cancel' hr.2
  · intro k hk
    push_cast
    rw [← mul_inv]

theorem bftb_sum_card_divisors_div_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r) ≤
      bftbHarmonicFactor R ^ 2 := by
  calc
    (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r)
      = ∑ r ∈ Finset.Icc 1 R,
          ∑ e ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hset : r.divisors = (Finset.Icc 1 R).filter (fun e => e ∣ r) := by
          ext e
          rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · intro he'
            exact ⟨⟨Nat.pos_of_dvd_of_pos he'.1 (Finset.mem_Icc.mp hr).1,
              (Nat.le_of_dvd (by omega : 0 < r) he'.1).trans
                (Finset.mem_Icc.mp hr).2⟩, he'.1⟩
          · intro he'
            exact ⟨he'.2, Nat.ne_of_gt (Finset.mem_Icc.mp hr).1⟩
        rw [hset, div_eq_mul_inv]
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul,
          Finset.sum_filter]
        simp
    _ = ∑ e ∈ Finset.Icc 1 R,
          ∑ r ∈ Finset.Icc 1 R, if e ∣ r then ((r : ℝ)⁻¹) else 0 := by
        exact Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * bftbHarmonicFactor (R / e) := by
        apply Finset.sum_congr rfl
        intro e he'
        exact bftb_sum_inv_multiples_Icc R e (Finset.mem_Icc.mp he').1
    _ ≤ ∑ e ∈ Finset.Icc 1 R,
          (e : ℝ)⁻¹ * bftbHarmonicFactor R := by
        apply Finset.sum_le_sum
        intro e he'
        apply mul_le_mul_of_nonneg_left
        · unfold bftbHarmonicFactor
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.div_le_self R e)
          · intro k hk hnot
            positivity
        · positivity
    _ = bftbHarmonicFactor R ^ 2 := by
        rw [bftbHarmonicFactor, ← Finset.sum_mul]
        ring

theorem bftb_sum_inv_totient_le_harmonic_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, ((r.totient : ℝ)⁻¹)) ≤
      bftbHarmonicFactor R ^ 2 := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) / r := by
      apply Finset.sum_le_sum
      intro r hr
      simpa [one_div] using
        bftb_inv_totient_le_card_divisors_div (Finset.mem_Icc.mp hr).1
    _ ≤ _ := bftb_sum_card_divisors_div_le_harmonic_sq R

theorem bftb_sum_inv_totient_le_one_add_log_sq (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, ((r.totient : ℝ)⁻¹)) ≤
      (1 + Real.log R) ^ 2 := by
  refine (bftb_sum_inv_totient_le_harmonic_sq R).trans ?_
  have hH : 0 ≤ bftbHarmonicFactor R :=
    bftbHarmonicFactor_nonneg R
  have hle : bftbHarmonicFactor R ≤ 1 + Real.log R :=
    bftbHarmonicFactor_le_one_add_log R
  have hK : 0 ≤ 1 + Real.log R := hH.trans hle
  exact (sq_le_sq₀ hH hK).2 hle

end

end OmegaBalance
