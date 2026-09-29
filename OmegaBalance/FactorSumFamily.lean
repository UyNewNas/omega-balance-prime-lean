import OmegaBalance.FactorSum

/-!
# Certified constructions of prime-factor-sum balanced centers

The five-prime theorem has explicit prime hypotheses. It does not assert
infinitude and does not assume Schinzel's hypothesis. The underlying
cofactor construction is attributed to Pomerance in the research notes.
-/

namespace OmegaBalance

def sumFamilyU (t : ℕ) : ℕ := 2 * t + 1
def sumFamilyV (t : ℕ) : ℕ := 15 * t + 8
def sumFamilyQ (t : ℕ) : ℕ := 390 * t ^ 2 + 238 * t + 17
def sumFamilyR (t : ℕ) : ℕ := 390 * t ^ 2 + 225 * t + 16
def sumFamilyCenter (t : ℕ) : ℕ := 23400 * t ^ 3 + 25980 * t ^ 2 + 8160 * t + 511

/-- The two fixed cofactors in the Pomerance-style inverse construction. -/
def sumFamilyA (t : ℕ) : ℕ := 15 * sumFamilyU t
def sumFamilyB (t : ℕ) : ℕ := 2 * sumFamilyV t
def sumFamilyD (t : ℕ) : ℕ := 13 * t + 1

theorem sumFamily_B_eq_A_add_one (t : ℕ) :
    sumFamilyB t = sumFamilyA t + 1 := by
  simp only [sumFamilyA, sumFamilyB, sumFamilyU, sumFamilyV]
  ring

/-- The inverse-construction denominator is exactly one, in signed arithmetic. -/
theorem sumFamily_B_sub_A_eq_one (t : ℕ) :
    (sumFamilyB t : ℤ) - sumFamilyA t = 1 := by
  have h := sumFamily_B_eq_A_add_one t
  omega

theorem sumFamily_Q_inverse (t : ℕ) :
    sumFamilyQ t = 1 + sumFamilyB t * sumFamilyD t := by
  simp only [sumFamilyQ, sumFamilyB, sumFamilyV, sumFamilyD]
  ring

theorem sumFamily_R_inverse (t : ℕ) :
    sumFamilyR t = 1 + sumFamilyA t * sumFamilyD t := by
  simp only [sumFamilyR, sumFamilyA, sumFamilyU, sumFamilyD]
  ring

theorem sumFamily_Q_sub_R (t : ℕ) :
    (sumFamilyQ t : ℤ) - sumFamilyR t = sumFamilyD t := by
  simp only [sumFamilyQ, sumFamilyR, sumFamilyD]
  push_cast
  ring

/-! ### Nelson–Penney–Pomerance family: the prime-center obstruction -/

def nppFamilyS (k : ℕ) : ℕ := 2 * k + 1
def nppFamilyB (k : ℕ) : ℕ := 8 * k + 5
def nppFamilyQ (k : ℕ) : ℕ := 48 * k ^ 2 + 24 * k - 1
def nppFamilyR (k : ℕ) : ℕ := 48 * k ^ 2 + 30 * k - 1
def nppFamilyCenter (k : ℕ) : ℕ :=
  768 * k ^ 3 + 864 * k ^ 2 + 224 * k - 9

/-- Modulo three, one of the center, `s`, or `b` is always obstructed. -/
theorem nppFamily_mod_three_obstruction (k : ℕ) :
    3 ∣ nppFamilyCenter k ∨ 3 ∣ nppFamilyS k ∨ 3 ∣ nppFamilyB k := by
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with hk | hk | hk
  · left
    have hkdiv : 3 ∣ k := Nat.dvd_iff_mod_eq_zero.mpr hk
    rcases hkdiv with ⟨j, rfl⟩
    by_cases hj : j = 0
    · subst j
      norm_num [nppFamilyCenter]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      let X : ℕ := 6912 * j ^ 3 + 2592 * j ^ 2 + 224 * j
      have hpre :
          768 * (3 * j) ^ 3 + 864 * (3 * j) ^ 2 + 224 * (3 * j) = 3 * X := by
        simp only [X]
        ring
      have hX : 3 ≤ X := by
        simp only [X]
        nlinarith
      rw [nppFamilyCenter, hpre]
      refine ⟨X - 3, ?_⟩
      omega
  · right; left
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [nppFamilyS, Nat.add_mod, Nat.mul_mod, hk]
  · right; right
    rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [nppFamilyB, Nat.add_mod, Nat.mul_mod, hk]

/-- If the two linear inputs are prime for `k ≥ 2`, modulo three is forced onto the center. -/
theorem nppFamily_three_dvd_center_of_linear_primes {k : ℕ} (hk : 2 ≤ k)
    (hs : (nppFamilyS k).Prime) (hb : (nppFamilyB k).Prime) :
    3 ∣ nppFamilyCenter k := by
  rcases nppFamily_mod_three_obstruction k with hc | hs3 | hb3
  · exact hc
  · have hh := hs.eq_one_or_self_of_dvd 3 hs3
    rcases hh with hh | hh
    · norm_num at hh
    · simp only [nppFamilyS] at hh
      omega
  · have hh := hb.eq_one_or_self_of_dvd 3 hb3
    rcases hh with hh | hh
    · norm_num at hh
    · simp only [nppFamilyB] at hh
      omega

/-- The classical four-prime construction cannot simultaneously have a prime center for `k ≥ 2`. -/
theorem nppFamily_no_prime_center {k : ℕ} (hk : 2 ≤ k)
    (hs : (nppFamilyS k).Prime) (hb : (nppFamilyB k).Prime)
    (_hq : (nppFamilyQ k).Prime) (_hr : (nppFamilyR k).Prime) :
    ¬ (nppFamilyCenter k).Prime := by
  intro hp
  have hd := nppFamily_three_dvd_center_of_linear_primes hk hs hb
  have hh := hp.eq_one_or_self_of_dvd 3 hd
  rcases hh with hh | hh
  · norm_num at hh
  · have hkpos : 0 < k := by omega
    have hkpow : 0 < k ^ 3 := pow_pos hkpos 3
    simp only [nppFamilyCenter] at hh
    omega

/-- Records five primality hypotheses, without asserting their existence. -/
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
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

/-- Five simultaneous prime values give a sum-balanced prime. -/
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

/-- Exact criterion even when the two quadratic values are composite. -/
theorem sumFamily_defect_identity {t : ℕ}
    (hu : (sumFamilyU t).Prime) (hv : (sumFamilyV t).Prime) :
    primeFactorSumDiff (sumFamilyCenter t) =
      primeFactorDefect (sumFamilyQ t) - primeFactorDefect (sumFamilyR t) := by
  have h15 : primeFactorSum 15 = 8 := by
    change primeFactorSum (3 * 5) = 8
    rw [primeFactorSum_mul (by norm_num) (by norm_num),
      primeFactorSum_prime Nat.prime_three,
      primeFactorSum_prime (by norm_num : Nat.Prime 5)]
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

/-- Division-free cofactor inversion, with signed arithmetic. -/
theorem sumCofactor_inverse_identity {A B q r d : ℤ}
    (hadj : B * r - A * q = 1) (hd : q - r = d) :
    (B - A) * r = 1 + A * d ∧ (B - A) * q = 1 + B * d := by
  subst d
  constructor <;> nlinarith

/-- Exact algebra behind the level-five divisor-pair construction. -/
theorem doubleFactorPair_identity (K L r s : ℤ) :
    (4 * r - K) * (4 * s - K) =
      K * (K - 4 * L) + 4 * (4 * r * s - K * (r + s - L)) := by
  ring

theorem doubleFactorPair_iff {K L r s d e : ℤ} (hd : d = r + s - L) :
    (4 * r - K) * (4 * s - K) = K * (K - 4 * L) + 4 * e ↔
      4 * r * s - K * d = e := by
  rw [doubleFactorPair_identity, hd]
  constructor <;> intro h <;> nlinarith

/-! ### Local admissibility at the four small primes -/

/-- None of the five family values vanishes modulo `ell` at parameter `t`. -/
def SumFamilyAvoidsPrime (ell t : ℕ) : Prop :=
  ¬ ell ∣ sumFamilyU t ∧ ¬ ell ∣ sumFamilyV t ∧
  ¬ ell ∣ sumFamilyQ t ∧ ¬ ell ∣ sumFamilyR t ∧
  ¬ ell ∣ sumFamilyCenter t

/-- Exact allowed residue modulo 2. -/
theorem sumFamily_mod_two_table {t : ℕ} (ht : t < 2) :
    SumFamilyAvoidsPrime 2 t ↔ t = 1 := by
  interval_cases t <;>
    norm_num [SumFamilyAvoidsPrime, sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR,
      sumFamilyCenter]

/-- Exact allowed residues modulo 3. -/
theorem sumFamily_mod_three_table {t : ℕ} (ht : t < 3) :
    SumFamilyAvoidsPrime 3 t ↔ t = 0 ∨ t = 2 := by
  interval_cases t <;>
    norm_num [SumFamilyAvoidsPrime, sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR,
      sumFamilyCenter]

/-- Exact allowed residues modulo 5. -/
theorem sumFamily_mod_five_table {t : ℕ} (ht : t < 5) :
    SumFamilyAvoidsPrime 5 t ↔ t = 0 ∨ t = 3 ∨ t = 4 := by
  interval_cases t <;>
    norm_num [SumFamilyAvoidsPrime, sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR,
      sumFamilyCenter]

/-- Exact allowed residues modulo 7. -/
theorem sumFamily_mod_seven_table {t : ℕ} (ht : t < 7) :
    SumFamilyAvoidsPrime 7 t ↔ t = 4 ∨ t = 5 := by
  interval_cases t <;>
    norm_num [SumFamilyAvoidsPrime, sumFamilyU, sumFamilyV, sumFamilyQ, sumFamilyR,
      sumFamilyCenter]

/-- The explicit small-prime part of the Schinzel admissibility check. -/
theorem sumFamily_small_prime_admissible {ell : ℕ}
    (h : ell = 2 ∨ ell = 3 ∨ ell = 5 ∨ ell = 7) :
    ∃ t < ell, SumFamilyAvoidsPrime ell t := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨1, by norm_num, (sumFamily_mod_two_table (by norm_num)).2 rfl⟩
  · exact ⟨0, by norm_num, (sumFamily_mod_three_table (by norm_num)).2 (Or.inl rfl)⟩
  · exact ⟨0, by norm_num, (sumFamily_mod_five_table (by norm_num)).2 (Or.inl rfl)⟩
  · exact ⟨4, by norm_num, (sumFamily_mod_seven_table (by norm_num)).2 (Or.inl rfl)⟩

end OmegaBalance
