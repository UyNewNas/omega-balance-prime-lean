import OmegaBalance.FactorSumFamily

/-!
# Necessary conditions and recovery for the Ruth--Aaron cofactor construction

The classical cofactor formula is attributed to Pomerance in
`docs/sum_balance/research_round2.md`. Signed identities use integers;
primality and positivity are never inferred from an algebraic solution.
-/

namespace OmegaBalance

/-- Adjacent products force their retained cofactors to be coprime. -/
theorem sumCofactor_coprime {A B q r : ℕ} (hadj : B * r = A * q + 1) :
    Nat.Coprime A B := by
  change Nat.gcd A B = 1
  apply Nat.dvd_one.mp
  apply Nat.dvd_iff_mod_eq_zero.mpr
  have hA := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left A B)
  have hB := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right A B)
  have hh := congrArg (fun n : ℕ => n % Nat.gcd A B) hadj
  simpa [Nat.mul_mod, Nat.add_mod, hA, hB] using hh.symm

/-- Equal cofactors cannot give both adjacency and factor-sum balance. -/
theorem sumCofactor_ne {A B q r : ℕ} (hadj : B * r = A * q + 1)
    (hsum : primeFactorSum A + q = primeFactorSum B + r) : A ≠ B := by
  intro he
  subst B
  have hqr : q = r := by omega
  rw [hqr] at hadj
  omega

/-- The two numerators are divisible by the signed cofactor difference. -/
theorem sumCofactor_divisibility {A B q r d : ℤ}
    (hadj : B * r - A * q = 1) (hd : q - r = d) :
    (B - A) ∣ 1 + A * d ∧ (B - A) ∣ 1 + B * d := by
  obtain ⟨hr, hq⟩ := sumCofactor_inverse_identity hadj hd
  exact ⟨⟨r, hr.symm⟩, ⟨q, hq.symm⟩⟩

/-- Signed cofactor inversion is reversible when the denominator is nonzero. -/
theorem sumCofactor_inverse_iff {A B q r d : ℤ} (hne : A ≠ B) :
    (B * r - A * q = 1 ∧ q - r = d) ↔
      ((B - A) * r = 1 + A * d ∧ (B - A) * q = 1 + B * d) := by
  constructor
  · rintro ⟨hadj, hd⟩
    exact sumCofactor_inverse_identity hadj hd
  · rintro ⟨hr, hq⟩
    have hzero : (B - A) * (q - r - d) = 0 := by nlinarith
    have hden : B - A ≠ 0 := by omega
    have hd : q - r = d := by
      have hz := (mul_eq_zero.mp hzero).resolve_left hden
      omega
    exact ⟨by nlinarith, hd⟩

/-- Positive prime-sized factors make the cofactor and sum differences agree in sign. -/
theorem sumCofactor_sign {A B q r d : ℤ}
    (hA : 0 < A) (hB : 0 < B) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hne : A ≠ B) (hadj : B * r - A * q = 1) (hd : q - r = d) :
    0 < (B - A) * d := by
  have hi := (sumCofactor_inverse_identity hadj hd).1
  rcases lt_or_gt_of_ne hne with hab | hab
  · have hden : 1 ≤ B - A := by omega
    have hprod : 2 ≤ (B - A) * r := by nlinarith
    have hdpos : 0 < d := by
      by_contra! h
      have hnonpos : A * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h
      linarith
    exact mul_pos (by omega) hdpos
  · have hden : B - A ≤ -1 := by omega
    have hprod : (B - A) * r ≤ -2 := by nlinarith
    have hdneg : d < 0 := by
      by_contra! h
      have hnonneg : 0 ≤ A * d := mul_nonneg (by omega) h
      linarith
    exact mul_pos_of_neg_of_neg (by omega) hdneg

/-- With odd selected factors the two cofactors have opposite parity. -/
theorem sumCofactor_opposite_parity {A B q r : ℕ}
    (hadj : B * r = A * q + 1) (hq : q % 2 = 1) (hr : r % 2 = 1) :
    A % 2 ≠ B % 2 := by
  have hh := congrArg (fun n : ℕ => n % 2) hadj
  norm_num [Nat.mul_mod, Nat.add_mod, hq, hr] at hh
  omega

/-- The factor-sum difference is even when both selected factors are odd. -/
theorem sumCofactor_even_sum_difference {A B q r : ℕ}
    (hsum : primeFactorSum A + q = primeFactorSum B + r)
    (hq : q % 2 = 1) (hr : r % 2 = 1) :
    ((primeFactorSum B : ℤ) - primeFactorSum A) % 2 = 0 := by
  omega

/-- Reconstruct a valid center from division-free inverse equations and prime factors. -/
theorem sumCofactor_recover_balanced {A B q r : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hne : A ≠ B)
    (hq : q.Prime) (hr : r.Prime)
    (hinv : ((B : ℤ) - A) * r = 1 + A * ((primeFactorSum B : ℤ) - primeFactorSum A) ∧
      ((B : ℤ) - A) * q = 1 + B * ((primeFactorSum B : ℤ) - primeFactorSum A))
    (hp : (2 * (A * q) + 1).Prime) :
    IsPrimeFactorSumBalancedPrime (2 * (A * q) + 1) := by
  have hneZ : (A : ℤ) ≠ B := by exact_mod_cast hne
  obtain ⟨hadjZ, hdiff⟩ := (sumCofactor_inverse_iff hneZ).mpr hinv
  have hadjZ' : (B : ℤ) * r = A * q + 1 := by linarith
  have hadj : B * r = A * q + 1 := by exact_mod_cast hadjZ'
  have hsum : primeFactorSum A + q = primeFactorSum B + r := by omega
  exact primeFactorSum_cofactor_construction hA hB hq hr hadj hsum hp

/-- Recovery form for the level-five divisor-pair equation, without truncated subtraction. -/
theorem doubleFactorPair_recover {K L x y r s d e : ℤ}
    (hx : x + K = 4 * r) (hy : y + K = 4 * s)
    (hxy : x * y = K * (K - 4 * L) + 4 * e) (hd : d = r + s - L) :
    4 * r * s - K * d = e := by
  apply (doubleFactorPair_iff hd).mp
  have hx' : 4 * r - K = x := by omega
  have hy' : 4 * s - K = y := by omega
  simpa only [hx', hy'] using hxy

end OmegaBalance
