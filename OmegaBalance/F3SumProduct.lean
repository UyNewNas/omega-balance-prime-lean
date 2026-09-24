import OmegaBalance.F3Powers

/-!
# Opposite levels: sum/product dichotomy and a refined gap lattice

These are arithmetic implications, not prime-pair existence statements.
The refined gap requires the additional product-depth hypothesis.
-/

namespace OmegaBalance

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem f3_positive_level {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hf : f3 n = (k : ℤ)) : n % 3 = 2 ∧ v3 (n + 1) = k := by
  have hpos : 0 < f3 n := by rw [hf]; exact_mod_cast hk
  have hm : n % 3 = 2 := by
    by_contra h
    have cases : n % 3 = 0 ∨ n % 3 = 1 := by omega
    rcases cases with h0 | h1
    · have := f3_of_mod_three_zero hn h0
      omega
    · have := (f3_of_mod_three_one hn h1).2
      omega
  refine ⟨hm, ?_⟩
  have hv := (f3_of_mod_three_two hn hm).1
  rw [hf] at hv
  exact_mod_cast hv.symm

theorem f3_negative_level {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hf : f3 n = -(k : ℤ)) : n % 3 = 1 ∧ v3 (n - 1) = k := by
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have hneg : f3 n < 0 := by rw [hf]; omega
  have hm : n % 3 = 1 := by
    by_contra h
    have cases : n % 3 = 0 ∨ n % 3 = 2 := by omega
    rcases cases with h0 | h2
    · have := f3_of_mod_three_zero hn h0
      omega
    · have := (f3_of_mod_three_two hn h2).2
      omega
  refine ⟨hm, ?_⟩
  have hv := (f3_of_mod_three_one hn hm).1
  rw [hf] at hv
  have hcast : (v3 (n - 1) : ℤ) = k := by omega
  exact_mod_cast hcast

theorem pow_three_dvd_of_le_v3 {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ v3 n) :
    3 ^ k ∣ n := by
  apply (padicValNat_dvd_iff_le hn).mpr
  simpa only [v3_eq_padic] using hk

/-- An exact valuation has a positive unit cofactor. -/
theorem v3_exact_factor {n k : ℕ} (hn : n ≠ 0) (hv : v3 n = k) :
    ∃ a : ℕ, 0 < a ∧ ¬ 3 ∣ a ∧ n = 3 ^ k * a := by
  obtain ⟨a, ha⟩ := pow_three_dvd_of_le_v3 hn (by omega : k ≤ v3 n)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hn ha
  have he := v3_mul (a := 3 ^ k) (b := a) (pow_ne_zero _ (by decide)) ha0
  rw [← ha, hv, v3_pow_three] at he
  have hz : v3 a = 0 := by omega
  refine ⟨a, Nat.pos_of_ne_zero ha0, ?_, ha⟩
  intro hd
  have := v3_pos_of_dvd ha0 hd
  omega

/-- Exactly one of the sum and product-plus-one remains at the input level. -/
theorem f3_opposite_sum_product {p q k : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hk : 0 < k) (hfp : f3 p = (k : ℤ)) (hfq : f3 q = -(k : ℤ)) :
    (v3 (p + q) = k ∧ k < v3 (p * q + 1)) ∨
    (k < v3 (p + q) ∧ v3 (p * q + 1) = k) := by
  obtain ⟨hpmod, hpv⟩ := f3_positive_level hp hk hfp
  obtain ⟨_, hqv⟩ := f3_negative_level hq hk hfq
  obtain ⟨a, ha, ha3, hpa⟩ := v3_exact_factor (by omega) hpv
  obtain ⟨b, hb, hb3, hqb⟩ := v3_exact_factor (by omega) hqv
  have hqb' : q = 3 ^ k * b + 1 := by omega
  have hsum : p + q = 3 ^ k * (a + b) := by nlinarith [hpa, hqb']
  have hprod : p * q + 1 = 3 ^ k * (a + p * b) := by
    rw [hqb']
    nlinarith [hpa]
  have hs : v3 (p + q) = k + v3 (a + b) := by
    rw [hsum, v3_mul (pow_ne_zero _ (by decide)) (by omega), v3_pow_three]
  have ht : v3 (p * q + 1) = k + v3 (a + p * b) := by
    rw [hprod, v3_mul (pow_ne_zero _ (by decide)) (by omega), v3_pow_three]
  have har : a % 3 ≠ 0 := fun h => ha3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hbr : b % 3 ≠ 0 := fun h => hb3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hac : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hbc : b % 3 = 1 ∨ b % 3 = 2 := by omega
  have cases : (¬ 3 ∣ a + b ∧ 3 ∣ a + p * b) ∨
      (3 ∣ a + b ∧ ¬ 3 ∣ a + p * b) := by
    rcases hac with h | h <;> rcases hbc with h' | h' <;>
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hpmod, h, h']
  rcases cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hz := v3_eq_zero_of_not_dvd h1
    have hv := v3_pos_of_dvd (by omega : a + p * b ≠ 0) h2
    exact Or.inl ⟨by omega, by omega⟩
  · have hv := v3_pos_of_dvd (by omega : a + b ≠ 0) h1
    have hz := v3_eq_zero_of_not_dvd h2
    exact Or.inr ⟨by omega, by omega⟩

theorem f3_opposite_sum_product_min {p q k : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hk : 0 < k) (hfp : f3 p = (k : ℤ)) (hfq : f3 q = -(k : ℤ)) :
    min (v3 (p + q)) (v3 (p * q + 1)) = k ∧
      v3 (p + q) ≠ v3 (p * q + 1) := by
  rcases f3_opposite_sum_product hp hq hk hfp hfq with h | h <;> omega

theorem f3_twin_product_of_mod {n : ℕ} (hn : 1 < n) (hm : n % 3 = 2) :
    f3 (n * (n + 2)) = 2 * f3 n := by
  have hprod : 1 < n * (n + 2) := by nlinarith
  have hmod : (n * (n + 2)) % 3 = 2 := by
    norm_num [Nat.mul_mod, Nat.add_mod, hm]
  rw [(f3_of_mod_three_two hprod hmod).1, (f3_of_mod_three_two hn hm).1]
  have hid : n * (n + 2) + 1 = (n + 1) * (n + 1) := by ring
  rw [hid, v3_mul (by omega) (by omega), Nat.cast_add]
  ring

theorem f3_twin_product {p : ℕ} (hp : p.Prime) (hq : (p + 2).Prime) (h3 : 3 < p) :
    f3 (p * (p + 2)) = 2 * f3 p :=
  f3_twin_product_of_mod (by omega) (twin_mod_three hp hq h3).1

/-- Additional product information refines the gap lattice to 3^(2k). -/
theorem f3_product_refined_gap {p q k : ℕ} (hp : 1 < p) (hq : p < q)
    (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hk : 0 < k)
    (hfp : f3 p = (k : ℤ)) (hfq : f3 q = -(k : ℤ))
    (hprod : f3 (p * q) = (2 * k : ℕ)) :
    ∃ r : ℕ, q = p + 2 + 2 * 3 ^ (2 * k) * r := by
  have hq1 : 1 < q := by omega
  have hgap : p + 2 ≤ q := by omega
  have hpv := (f3_positive_level hp hk hfp).2
  have hqv := (f3_negative_level hq1 hk hfq).2
  have hpqv := (f3_positive_level (by nlinarith : 1 < p * q)
    (by omega : 0 < 2 * k) hprod).2
  have hpd : 3 ^ k ∣ p + 1 := pow_three_dvd_of_le_v3 (by omega) (by omega)
  have hqd : 3 ^ k ∣ q - 1 := pow_three_dvd_of_le_v3 (by omega) (by omega)
  have hmul : 3 ^ (2 * k) ∣ (p + 1) * (q - 1) := by
    have hh := Nat.mul_dvd_mul hpd hqd
    simpa only [← pow_add, ← two_mul] using hh
  have hprd : 3 ^ (2 * k) ∣ p * q + 1 :=
    pow_three_dvd_of_le_v3 (by omega) (by omega)
  have hid : (p + 1) * (q - 1) - (p * q + 1) = q - p - 2 := by
    have hqsub : q - 1 + 1 = q := by omega
    have hdsub : q - p - 2 + p + 2 = q := by omega
    have he : (p + 1) * (q - 1) = (p * q + 1) + (q - p - 2) := by
      nlinarith [hqsub, hdsub]
    omega
  have hd : 3 ^ (2 * k) ∣ q - p - 2 := by
    rw [← hid]
    exact Nat.dvd_sub hmul hprd
  obtain ⟨t, ht⟩ := hd
  have hmodpow : 3 ^ (2 * k) % 2 = 1 := by norm_num [Nat.pow_mod]
  have hmodt : t % 2 = 0 := by
    have hdelta : (q - p - 2) % 2 = 0 := by omega
    rw [ht, Nat.mul_mod, hmodpow] at hdelta
    simpa using hdelta
  have hte : t = 2 * (t / 2) := by omega
  refine ⟨t / 2, ?_⟩
  rw [hte] at ht
  have hdsub : q - p - 2 + p + 2 = q := by omega
  nlinarith [ht, hdsub]

theorem f3_product_gap_dichotomy {p q k : ℕ} (hp : 1 < p) (hq : p < q)
    (hpo : p % 2 = 1) (hqo : q % 2 = 1) (hk : 0 < k)
    (hfp : f3 p = (k : ℤ)) (hfq : f3 q = -(k : ℤ))
    (hprod : f3 (p * q) = (2 * k : ℕ)) :
    q = p + 2 ∨ p + 2 + 2 * 3 ^ (2 * k) ≤ q := by
  obtain ⟨r, hr⟩ := f3_product_refined_gap hp hq hpo hqo hk hfp hfq hprod
  by_cases hz : r = 0
  · left; simpa [hz] using hr
  · right
    have : 1 ≤ r := by omega
    nlinarith [hr]

end OmegaBalance
