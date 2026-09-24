import OmegaBalance.FactorSum

/-!
# Certified constructions of prime-factor-sum balanced centers

The five-prime theorem is an implication with explicit prime hypotheses.
It is not an infinitude theorem and does not assume Schinzel's hypothesis.
The cofactor construction is the one attributed to Pomerance in the notes.
-/

namespace OmegaBalance

def sumFamilyU (t : ℕ) : ℕ := 2 * t + 1
def sumFamilyV (t : ℕ) : ℕ := 15 * t + 8
def sumFamilyQ (t : ℕ) : ℕ := 390 * t ^ 2 + 238 * t + 17
def sumFamilyR (t : ℕ) : ℕ := 390 * t ^ 2 + 225 * t + 16
def sumFamilyCenter (t : ℕ) : ℕ := 23400 * t ^ 3 + 25980 * t ^ 2 + 8160 * t + 511

/-- This predicate only RECORDS hypotheses; it asserts no existence. -/
def SumFamilyPrimeValues (t : ℕ) : Prop :=
  (sumFamilyU t).Prime ∧ (sumFamilyV t).Prime ∧
  (sumFamilyQ t).Prime ∧ (sumFamilyR t).Prime ∧ (sumFamilyCenter t).Prime

theorem sumFamily_adjacent (t : ℕ) :
    (2 * sumFamilyV t) * sumFamilyR t = (15 * sumFamilyU t) * sumFamilyQ t + 1 := by
  simp only [sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR]
  ring

theorem sumFamily_center_eq (t : ℕ) :
    sumFamilyCenter t = 2 * ((15 * sumFamilyU t) * sumFamilyQ t) + 1 := by
  simp only [sumFamilyCenter, sumFamilyU, sumFamilyQ]
  ring

theorem sumFamily_pred (t : ℕ) :
    sumFamilyCenter t - 1 = 2 * 3 * 5 * sumFamilyU t * sumFamilyQ t := by
  rw [sumFamily_center_eq]
  simp only [Nat.add_sub_cancel]
  ring

theorem sumFamily_succ (t : ℕ) :
    sumFamilyCenter t + 1 = 2 * 2 * sumFamilyV t * sumFamilyR t := by
  simp only [sumFamilyCenter, sumFamilyV, sumFamilyR]
  ring

theorem sumFamily_factor_sum_identity (t : ℕ) :
    10 + sumFamilyU t + sumFamilyQ t = 4 + sumFamilyV t + sumFamilyR t := by
  simp only [sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR]
  ring

theorem sumFamily_left_profile {t : ℕ}
    (hu : (sumFamilyU t).Prime) (hq : (sumFamilyQ t).Prime) :
    primeFactorSum (sumFamilyCenter t - 1) = 10 + sumFamilyU t + sumFamilyQ t ∧
    bigOmega (sumFamilyCenter t - 1) = 5 := by
  have hp : ∀ z ∈ [2, 3, 5, sumFamilyU t, sumFamilyQ t], z.Prime := by
    intro z hz
    simp only [List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hu | exact hq | norm_num
  have he : [2, 3, 5, sumFamilyU t, sumFamilyQ t].prod = sumFamilyCenter t - 1 := by
    rw [sumFamily_pred]
    simp only [List.prod_cons, List.prod_nil]
    ring
  have hs := primeFactorSum_of_factors he hp
  have ho := bigOmega_of_factors he hp
  norm_num at hs ho
  exact ⟨by omega, ho⟩

theorem sumFamily_right_profile {t : ℕ}
    (hv : (sumFamilyV t).Prime) (hr : (sumFamilyR t).Prime) :
    primeFactorSum (sumFamilyCenter t + 1) = 4 + sumFamilyV t + sumFamilyR t ∧
    bigOmega (sumFamilyCenter t + 1) = 4 := by
  have hp : ∀ z ∈ [2, 2, sumFamilyV t, sumFamilyR t], z.Prime := by
    intro z hz
    simp only [List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      first | exact hv | exact hr | norm_num
  have he : [2, 2, sumFamilyV t, sumFamilyR t].prod = sumFamilyCenter t + 1 := by
    rw [sumFamily_succ]
    simp only [List.prod_cons, List.prod_nil]
    ring
  have hs := primeFactorSum_of_factors he hp
  have ho := bigOmega_of_factors he hp
  norm_num at hs ho
  exact ⟨by omega, ho⟩

/-- Four prime factors imply balance; center primality is not needed here. -/
theorem sumFamily_balanced {t : ℕ}
    (hu : (sumFamilyU t).Prime) (hv : (sumFamilyV t).Prime)
    (hq : (sumFamilyQ t).Prime) (hr : (sumFamilyR t).Prime) :
    IsPrimeFactorSumBalanced (sumFamilyCenter t) := by
  exact (sumFamily_left_profile hu hq).1.trans
    ((sumFamily_factor_sum_identity t).trans (sumFamily_right_profile hv hr).1.symm)

/-- Main construction: five simultaneous primes imply a sum-balanced prime. -/
theorem sumFamily_five_primes {t : ℕ} (h : SumFamilyPrimeValues t) :
    IsPrimeFactorSumBalancedPrime (sumFamilyCenter t) :=
  ⟨h.2.2.2.2, sumFamily_balanced h.1 h.2.1 h.2.2.1 h.2.2.2.1⟩

theorem sumFamily_omegaSum_eq_nine {t : ℕ} (h : SumFamilyPrimeValues t) :
    omegaSum (sumFamilyCenter t) = 9 := by
  simp [omegaSum, (sumFamily_left_profile h.1 h.2.2.1).2,
    (sumFamily_right_profile h.2.1 h.2.2.2.1).2]

theorem sumFamily_omegaDiff_eq_neg_one {t : ℕ} (h : SumFamilyPrimeValues t) :
    omegaDiff (sumFamilyCenter t) = -1 := by
  simp [omegaDiff, neighborDiff, (sumFamily_left_profile h.1 h.2.2.1).2,
    (sumFamily_right_profile h.2.1 h.2.2.2.1).2]

theorem sumFamily_not_omegaBalanced {t : ℕ} (h : SumFamilyPrimeValues t) :
    ¬ IsOmegaBalanced (sumFamilyCenter t) := by
  rw [← omegaDiff_eq_zero_iff, sumFamily_omegaDiff_eq_neg_one h]
  norm_num

/-- The same family also admits a precise criterion for composite q,r. -/
theorem sumFamily_defect_identity {t : ℕ}
    (hu : (sumFamilyU t).Prime) (hv : (sumFamilyV t).Prime) :
    primeFactorSumDiff (sumFamilyCenter t) =
      primeFactorDefect (sumFamilyQ t) - primeFactorDefect (sumFamilyR t) := by
  have h15 : primeFactorSum 15 = 8 := by
    have h := primeFactorSum_of_factors (n := 15) (l := [3, 5])
      (by norm_num) (by intro z hz; simp only [List.mem_cons, List.mem_singleton] at hz
                       rcases hz with rfl | rfl <;> norm_num)
    norm_num at h
    exact h
  have hA : 15 * sumFamilyU t ≠ 0 := mul_ne_zero (by norm_num) hu.ne_zero
  have hB : 2 * sumFamilyV t ≠ 0 := mul_ne_zero (by norm_num) hv.ne_zero
  have hq : sumFamilyQ t ≠ 0 := by unfold sumFamilyQ; omega
  have hr : sumFamilyR t ≠ 0 := by unfold sumFamilyR; omega
  rw [sumFamily_center_eq]
  apply primeFactorSum_cofactor_defect hA hB hq hr (sumFamily_adjacent t)
  rw [primeFactorSum_mul (by norm_num) hu.ne_zero,
    primeFactorSum_mul (by norm_num) hv.ne_zero,
    primeFactorSum_prime hu, primeFactorSum_prime hv, h15,
    primeFactorSum_prime Nat.prime_two]
  simp only [sumFamilyQ, sumFamilyR, sumFamilyU, sumFamilyV]
  push_cast
  ring

theorem sumFamily_balanced_iff_defect {t : ℕ}
    (hu : (sumFamilyU t).Prime) (hv : (sumFamilyV t).Prime) :
    IsPrimeFactorSumBalanced (sumFamilyCenter t) ↔
      primeFactorDefect (sumFamilyQ t) = primeFactorDefect (sumFamilyR t) := by
  rw [← primeFactorSumDiff_eq_zero_iff, sumFamily_defect_identity hu hv, sub_eq_zero]

/-- Division-free form of the general cofactor inversion formula. -/
theorem sumCofactor_inverse_identity {A B q r d : ℤ}
    (hadj : B * r - A * q = 1) (hd : q - r = d) :
    (B - A) * r = 1 + A * d ∧ (B - A) * q = 1 + B * d := by
  constructor <;> nlinarith [mul_eq_mul_left_iff.mp (congrArg (fun x => A * x) hd),
    congrArg (fun x => B * x) hd]

/-- Exact algebra behind the level-five divisor-pair construction. -/
theorem doubleFactorPair_identity (K L r s : ℤ) :
    (4 * r - K) * (4 * s - K) =
      K * (K - 4 * L) + 4 * (4 * r * s - K * (r + s - L)) := by
  ring

theorem doubleFactorPair_iff {K L r s d e : ℤ} (hd : d = r + s - L) :
    (4 * r - K) * (4 * s - K) = K * (K - 4 * L) + 4 * e ↔
      4 * r * s - K * d = e := by
  rw [doubleFactorPair_identity, hd]
  omega

end OmegaBalance
