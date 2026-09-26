import OmegaBalance.F3PrimeDensityExactPos

namespace OmegaBalance

/-- A prime on exact F₃ level -2 is automatically beyond the two exceptional
small primes. -/
lemma prime_gt_three_of_f3_eq_neg_two
    {q : ℕ} (hq : q.Prime) (hf : f3 q = -2) : 3 < q := by
  by_contra hnot
  have hq2 : 2 ≤ q := hq.two_le
  have hq23 : q = 2 ∨ q = 3 := by omega
  rcases hq23 with rfl | rfl
  · have hf2 : f3 2 = 1 := by
      have h := (f3_of_mod_three_two (n := 2) (by norm_num) (by norm_num)).1
      rw [h]
      simpa using v3_pow_three 1
    omega
  · have hv4 : v3 4 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
    have hv2 : v3 2 = 0 := v3_eq_zero_of_not_dvd (by norm_num)
    have hf3 : f3 3 = 0 := by
      simp [f3, neighborDiff, hv4, hv2]
    omega

/-- Exact level -2 splits into the two primitive classes 10 and 19 modulo 27. -/
theorem f3_prime_eq_neg_two_mod_twentyseven
    {q : ℕ} (hq : q.Prime) (hf : f3 q = -2) :
    q % 27 = 10 ∨ q % 27 = 19 := by
  have hq3 := prime_gt_three_of_f3_eq_neg_two hq hf
  have hf' : f3 q = -(2 : ℤ) := by simpa using hf
  have hres :=
    (f3_prime_eq_neg_level_iff_nested_residue
      (p := q) (k := 2) hq hq3 (by norm_num)).1 hf'
  norm_num at hres
  omega

/-- For a prime input on level -2, multiplication by 17 stays on the positive
side and has exact output level +2 precisely on the class 10 modulo 27. -/
theorem f3_seventeen_mul_eq_two_iff_mod_twentyseven_ten
    {q : ℕ} (hq : q.Prime) (hf : f3 q = -2) :
    f3 (17 * q) = 2 ↔ q % 27 = 10 := by
  have hq3 := prime_gt_three_of_f3_eq_neg_two hq hf
  have hf' : f3 q = -(2 : ℤ) := by simpa using hf
  have hres :=
    (f3_prime_eq_neg_level_iff_nested_residue
      (p := q) (k := 2) hq hq3 (by norm_num)).1 hf'
  norm_num at hres
  have hmods := f3_prime_eq_neg_two_mod_twentyseven hq hf
  have hqmod3 : q % 3 = 1 := by omega
  have hprodmod3 : (17 * q) % 3 = 2 := by
    norm_num [Nat.mul_mod, hqmod3]
  have hgt : 1 < 17 * q := by
    have := hq.two_le
    omega
  have hfprod := (f3_of_mod_three_two (n := 17 * q) hgt hprodmod3).1
  rw [hfprod]
  have hviff :=
    v3_eq_iff_pow_three_dvd_not_succ
      (n := 17 * q + 1) (k := 2) (by omega)
  norm_num at hviff
  have h9 : 9 ∣ 17 * q + 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  constructor
  · intro hout
    have hv : v3 (17 * q + 1) = 2 := by
      exact_mod_cast hout
    have hnot27 := (hviff.mp hv).2
    rcases hmods with h10 | h19
    · exact h10
    · exfalso
      apply hnot27
      apply Nat.dvd_iff_mod_eq_zero.mpr
      omega
  · intro h10
    have hnot27 : ¬ 27 ∣ 17 * q + 1 := by
      intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      omega
    have hv : v3 (17 * q + 1) = 2 :=
      hviff.mpr ⟨h9, hnot27⟩
    exact_mod_cast hv

end OmegaBalance
