import OmegaBalance.F3PrimeDensityMul17Count

namespace OmegaBalance

/-- Any multiplier-17 output on positive F₃ level at least three forces the
prime input onto exact level -2. This is the arithmetic bridge that removes
the input-condition bookkeeping for the higher DEN-2 branches. -/
theorem f3_seventeen_mul_high_level_implies_neg_two
    {q k : ℕ} (hq : q.Prime) (hk : 3 ≤ k)
    (hout : f3 (17 * q) = (k : ℤ)) :
    f3 q = -2 := by
  have hgt : 1 < 17 * q := by
    have hq2 := hq.two_le
    omega
  have hkpos : (0 : ℤ) < (k : ℤ) := by
    exact_mod_cast (show 0 < k by omega)
  have hprodpos : 0 < f3 (17 * q) := by
    rw [hout]
    exact hkpos
  have hprodmod3 : (17 * q) % 3 = 2 := by
    by_contra hne
    have hlt : (17 * q) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hcases : (17 * q) % 3 = 0 ∨ (17 * q) % 3 = 1 := by omega
    rcases hcases with h0 | h1
    · have hz := f3_of_mod_three_zero hgt h0
      omega
    · have hn := (f3_of_mod_three_one hgt h1).2
      omega
  have he := (f3_of_mod_three_two hgt hprodmod3).1
  have hv : v3 (17 * q + 1) = k := by
    rw [he] at hout
    exact_mod_cast hout
  have h27dvd : 27 ∣ 17 * q + 1 := by
    have hpow :=
      pow_three_dvd_of_le_v3
        (n := 17 * q + 1) (k := 3) (by omega) (by omega : 3 ≤ v3 (17 * q + 1))
    norm_num at hpow
    exact hpow
  have hzero : 17 * q + 1 ≡ 0 [MOD 27] :=
    Nat.modEq_zero_iff_dvd.mpr h27dvd
  have hnineteen : 17 * 19 + 1 ≡ 0 [MOD 27] := by
    norm_num [Nat.ModEq]
  have hadd : 17 * q + 1 ≡ 17 * 19 + 1 [MOD 27] :=
    hzero.trans hnineteen.symm
  have hmul : 17 * q ≡ 17 * 19 [MOD 27] :=
    Nat.ModEq.add_right_cancel' 1 hadd
  have hqmod : q ≡ 19 [MOD 27] :=
    Nat.ModEq.cancel_left_of_coprime
      (by norm_num : Nat.gcd 27 17 = 1) hmul
  have hq27 : q % 27 = 19 := by
    simpa [Nat.ModEq] using hqmod
  have hq9mod : q ≡ 19 [MOD 9] :=
    hqmod.of_dvd (by norm_num : 9 ∣ 27)
  have hq9 : q % 9 = 1 := by
    simpa [Nat.ModEq] using hq9mod
  have hq3 : 3 < q := by
    by_contra hnot
    have hq2 := hq.two_le
    have hcases : q = 2 ∨ q = 3 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hq9
  have hq27ne : q % 27 ≠ 1 := by omega
  have hf : f3 q = -(2 : ℤ) :=
    (f3_prime_eq_neg_level_iff_nested_residue
      (p := q) (k := 2) hq hq3 (by norm_num)).2 <| by
        constructor
        · simpa using hq9
        · simpa using hq27ne
  simpa using hf

/-- In the target DEN-2 indexing, every branch above the first one automatically
lies inside the conditioning population F₃(q) = -2. -/
theorem f3_seventeen_mul_eq_two_add_implies_neg_two
    {q j : ℕ} (hq : q.Prime) (hj : 0 < j)
    (hout : f3 (17 * q) = ((2 + j : ℕ) : ℤ)) :
    f3 q = -2 :=
  f3_seventeen_mul_high_level_implies_neg_two hq (by omega) hout

end OmegaBalance
