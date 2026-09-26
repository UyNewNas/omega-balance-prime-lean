import OmegaBalance.F3PrimeDensityMul17

open Filter Topology

namespace OmegaBalance

noncomputable def f3PrimeMul17EqTwoPrimes (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).filter fun q =>
    q.Prime ∧ f3 q = -2 ∧ f3 (17 * q) = 2

noncomputable def f3PrimeMul17EqTwoCountingReal (x : ℝ) : ℝ :=
  (f3PrimeMul17EqTwoPrimes x).card

theorem f3PrimeMul17EqTwoPrimes_eq_AP (x : ℝ) :
    f3PrimeMul17EqTwoPrimes x = f3APPrimes 27 10 x := by
  ext q
  simp only [f3PrimeMul17EqTwoPrimes, f3APPrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hrange, hq, hf, hout⟩
    exact ⟨hrange, hq,
      (f3_seventeen_mul_eq_two_iff_mod_twentyseven_ten hq hf).1 hout⟩
  · rintro ⟨hrange, hq, hmod⟩
    have hq3 : 3 < q := by omega
    have h9 : q % 9 = 1 := by omega
    have h27 : q % 27 ≠ 1 := by omega
    have hf' : f3 q = -(2 : ℤ) :=
      (f3_prime_eq_neg_level_iff_nested_residue
        (p := q) (k := 2) hq hq3 (by norm_num)).2 ⟨by
          norm_num
          exact h9, by
          norm_num
          exact h27⟩
    have hf : f3 q = -2 := by simpa using hf'
    exact ⟨hrange, hq, hf,
      (f3_seventeen_mul_eq_two_iff_mod_twentyseven_ten hq hf).2 hmod⟩

theorem f3PrimeMul17EqTwoCountingReal_eq_APCountingReal (x : ℝ) :
    f3PrimeMul17EqTwoCountingReal x =
      f3PrimeAPCountingReal 27 10 x := by
  rw [f3PrimeMul17EqTwoCountingReal,
    f3PrimeAPCountingReal_eq_card_apPrimes,
    f3PrimeMul17EqTwoPrimes_eq_AP]

lemma f3_totient_twentyseven : Nat.totient 27 = 18 := by
  have h := Nat.totient_prime_pow Nat.prime_three
    (by norm_num : 0 < (3 : ℕ))
  norm_num at h
  exact h

theorem f3PrimeMul17EqTwoCountingReal_normalized_tendsto :
    Tendsto
      (fun x : ℝ =>
        f3PrimeMul17EqTwoCountingReal x / (x / Real.log x))
      atTop (𝓝 (1 / 18 : ℝ)) := by
  have h :=
    f3PrimeAPCountingReal_normalized_tendsto
      (A := 27) (a := 10) (by norm_num) (by norm_num) (by norm_num)
  have h' := h.congr' <|
    Filter.Eventually.of_forall fun x => by
      exact congrArg (fun y : ℝ => y / (x / Real.log x))
        (f3PrimeMul17EqTwoCountingReal_eq_APCountingReal x).symm
  simpa [f3_totient_twentyseven, one_div] using h'

/-- The genuine conditional counting ratio inside the input population
`F₃(q)=-2`. It is totalized as a real quotient for small cutoffs where the
denominator may vanish; the limit theorem below only uses its eventual tail. -/
noncomputable def f3PrimeMul17EqTwoRelativeRatio (x : ℝ) : ℝ :=
  f3PrimeMul17EqTwoCountingReal x / f3PrimeNegLevelCountingReal 2 x

/-- Among primes with `F₃(q)=-2`, the multiplier-17 output branch
`F₃(17q)=2` has genuine relative natural density `1/2`.  The proof divides
the two already-proved `x / log x` asymptotics and then removes the common
normalization only on the eventual tail where it is nonzero. -/
theorem f3PrimeMul17EqTwoRelativeRatio_tendsto :
    Tendsto f3PrimeMul17EqTwoRelativeRatio atTop (𝓝 (1 / 2 : ℝ)) := by
  have hnum := f3PrimeMul17EqTwoCountingReal_normalized_tendsto
  have hden :=
    f3PrimeNegLevelCountingReal_normalized_tendsto
      (k := 2) (by norm_num)
  have hratio :
      Tendsto
        (fun x : ℝ =>
          (f3PrimeMul17EqTwoCountingReal x / (x / Real.log x)) /
            (f3PrimeNegLevelCountingReal 2 x / (x / Real.log x)))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    convert hnum.div hden (by norm_num : (1 / (3 : ℝ) ^ 2) ≠ 0) using 1 <;>
      norm_num
  refine hratio.congr' ?_
  have hden_ne :
      ∀ᶠ x : ℝ in atTop,
        f3PrimeNegLevelCountingReal 2 x / (x / Real.log x) ≠ 0 :=
    hden.eventually_ne (by norm_num : (1 / (3 : ℝ) ^ 2) ≠ 0)
  filter_upwards [hden_ne] with x hx
  have hscale : x / Real.log x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  simpa [f3PrimeMul17EqTwoRelativeRatio] using
    (div_div_div_cancel_right₀ hscale
      (f3PrimeMul17EqTwoCountingReal x)
      (f3PrimeNegLevelCountingReal 2 x))

/-- Seventeen stays coprime to every power of three. -/
lemma f3_seventeen_coprime_three_pow (m : ℕ) : Nat.Coprime 17 (3 ^ m) := by
  apply Nat.Coprime.pow_right
  norm_num

/-- The distinguished unit residue solving `17 a = -1` modulo `3^m`. -/
noncomputable def f3Mul17ResidueUnit (m : ℕ) : (ZMod (3 ^ m))ˣ :=
  -((ZMod.unitOfCoprime 17 (f3_seventeen_coprime_three_pow m))⁻¹)

/-- The distinguished multiplier-17 residue has the defining equation in
`ZMod (3^m)`. -/
lemma f3Mul17ResidueUnit_spec (m : ℕ) :
    (17 : ZMod (3 ^ m)) *
        (f3Mul17ResidueUnit m : ZMod (3 ^ m)) = -1 := by
  simp [f3Mul17ResidueUnit]

/-- Least natural representative of the distinguished multiplier-17 residue. -/
noncomputable def f3Mul17Residue (m : ℕ) : ℕ :=
  (f3Mul17ResidueUnit m : ZMod (3 ^ m)).val

lemma f3Mul17Residue_lt (m : ℕ) :
    f3Mul17Residue m < 3 ^ m := by
  letI : NeZero (3 ^ m) := ⟨by positivity⟩
  exact ZMod.val_lt _

lemma f3Mul17Residue_coprime (m : ℕ) :
    Nat.Coprime (f3Mul17Residue m) (3 ^ m) := by
  exact ZMod.val_coe_unit_coprime (f3Mul17ResidueUnit m)

/-- The representative really makes `17a+1` divisible by the modulus. -/
lemma pow_three_dvd_seventeen_mul_residue_add_one (m : ℕ) :
    3 ^ m ∣ 17 * f3Mul17Residue m + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  letI : NeZero (3 ^ m) := ⟨by positivity⟩
  rw [show (f3Mul17Residue m : ZMod (3 ^ m)) =
      (f3Mul17ResidueUnit m : ZMod (3 ^ m)) by
        exact ZMod.natCast_zmod_val _]
  rw [f3Mul17ResidueUnit_spec]
  simp

/-- Divisibility of `17q+1` by a power of three is exactly membership in the
distinguished multiplier-17 residue class. -/
theorem pow_three_dvd_seventeen_mul_add_one_iff_mod_eq_residue
    (m q : ℕ) :
    3 ^ m ∣ 17 * q + 1 ↔ q % (3 ^ m) = f3Mul17Residue m := by
  constructor
  · intro hqdiv
    have hq : 17 * q + 1 ≡ 0 [MOD 3 ^ m] :=
      Nat.modEq_zero_iff_dvd.mpr hqdiv
    have hr : 17 * f3Mul17Residue m + 1 ≡ 0 [MOD 3 ^ m] :=
      Nat.modEq_zero_iff_dvd.mpr
        (pow_three_dvd_seventeen_mul_residue_add_one m)
    have hmul : 17 * q ≡ 17 * f3Mul17Residue m [MOD 3 ^ m] :=
      Nat.ModEq.add_right_cancel' 1 (hq.trans hr.symm)
    have hgcd : Nat.gcd (3 ^ m) 17 = 1 := by
      rw [Nat.gcd_comm]
      exact (f3_seventeen_coprime_three_pow m).gcd_eq_one
    have hmod :=
      Nat.ModEq.cancel_left_of_coprime hgcd hmul
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (f3Mul17Residue_lt m)] using hmod
  · intro hmod
    have hq : q ≡ f3Mul17Residue m [MOD 3 ^ m] := by
      show q % (3 ^ m) = f3Mul17Residue m % (3 ^ m)
      simpa [Nat.mod_eq_of_lt (f3Mul17Residue_lt m)] using hmod
    have hsum :
        17 * q + 1 ≡ 17 * f3Mul17Residue m + 1 [MOD 3 ^ m] :=
      (hq.mul_left 17).add_right 1
    exact Nat.modEq_zero_iff_dvd.mp <|
      hsum.trans <| Nat.modEq_zero_iff_dvd.mpr
        (pow_three_dvd_seventeen_mul_residue_add_one m)

end OmegaBalance
