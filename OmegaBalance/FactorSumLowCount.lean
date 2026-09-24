import OmegaBalance.FactorSumLowAux
import OmegaBalance.FactorSumFamily

/-!
# Complete classification at total factor count at most eight

The proof first establishes an unrestricted bound p < 2000. Only then is
the finite kernel computation used. No external scan is an assumption.
-/

namespace OmegaBalance

set_option maxHeartbeats 2000000

/-- The half-neighbor count pattern (2,3) has bounded center. -/
theorem sumPair_two_three_bound {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huo : u % 2 = 1) (hve : v % 2 = 0) (hp : (u + v).Prime)
    (hadj : u + 1 = v ∨ v + 1 = u) (hsum : primeFactorSum u = primeFactorSum v)
    (hOu : bigOmega u = 2) (hOv : bigOmega v = 3) : u + v < 2000 := by
  obtain ⟨a, b, ha, hb, heU⟩ := bigOmega_eq_two_factors (by omega) hOu
  obtain ⟨r, s, hr, hs, heV⟩ := even_omega_three_shape hv hve hOv
  have hSU : primeFactorSum u = a + b := by
    rw [heU, primeFactorSum_mul ha.ne_zero hb.ne_zero, primeFactorSum_prime ha, primeFactorSum_prime hb]
  have hSV : primeFactorSum v = 2 + r + s := by
    rw [heV, primeFactorSum_mul (mul_ne_zero (by norm_num) hr.ne_zero) hs.ne_zero,
      primeFactorSum_mul (by norm_num) hr.ne_zero, primeFactorSum_prime Nat.prime_two,
      primeFactorSum_prime hr, primeFactorSum_prime hs]
  have hpar := primeFactorSum_odd_parity huo
  have hro := hr.eq_two_or_odd
  have hso := hs.eq_two_or_odd
  have hcases : (r = 2 ∧ s = 2) ∨ (r % 2 = 1 ∧ s % 2 = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | hrs
  · omega
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hs3 : 3 ≤ s := by have := hs.two_le; omega
  have h3p : 3 < u + v := by nlinarith [Nat.mul_le_mul ha.two_le hb.two_le]
  rcases three_dvd_adjacent_prime_sum hp h3p rfl hadj with hdu | hdv
  · have hd' : 3 ∣ a * b := by simpa [heU] using hdu
    have hbound := two_odd_factor_gap hr3 hs3
    rcases Nat.prime_three.dvd_mul.mp hd' with hda | hdb
    · have ha3 : a = 3 := ((ha.eq_one_or_self_of_dvd 3 hda).resolve_left (by norm_num)).symm
      subst a
      exfalso
      rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hbound, hadj]
    · have hb3 : b = 3 := ((hb.eq_one_or_self_of_dvd 3 hdb).resolve_left (by norm_num)).symm
      subst b
      exfalso
      rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hbound, hadj]
  · have hnu : ¬ 3 ∣ u := adjacent_not_common_dvd (by norm_num : 1 < 3) (by omega) hdv
    have ha5 : 5 ≤ a := prime_five_le_of_dvd_odd ha ⟨b, heU⟩ huo hnu
    have hb5 : 5 ≤ b := prime_five_le_of_dvd_odd hb ⟨a, by rw [heU]; ring⟩ huo hnu
    have hd' : 3 ∣ r ∨ 3 ∣ s := by
      have hh : 3 ∣ 2 * r * s := by simpa [heV] using hdv
      simpa [Nat.prime_three.dvd_mul] using hh
    rcases hd' with hdr | hds
    · have hr' : r = 3 := ((hr.eq_one_or_self_of_dvd 3 hdr).resolve_left (by norm_num)).symm
      subst r
      have hl : a * b + 29 ≤ 6 * (a + b) := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hh : 6 * (a + b) ≤ a * b + 31 := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hbound := low_pair_six_bound ha5 hb5 hl hh
      rw [← heU] at hbound
      omega
    · have hs' : s = 3 := ((hs.eq_one_or_self_of_dvd 3 hds).resolve_left (by norm_num)).symm
      subst s
      have hl : a * b + 29 ≤ 6 * (a + b) := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hh : 6 * (a + b) ≤ a * b + 31 := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hbound := low_pair_six_bound ha5 hb5 hl hh
      rw [← heU] at hbound
      omega

/-- The half-neighbor count pattern (2,4) has bounded center. -/
theorem sumPair_two_four_bound {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huo : u % 2 = 1) (hve : v % 2 = 0) (hp : (u + v).Prime)
    (hadj : u + 1 = v ∨ v + 1 = u) (hsum : primeFactorSum u = primeFactorSum v)
    (hOu : bigOmega u = 2) (hOv : bigOmega v = 4) : u + v < 2000 := by
  obtain ⟨a, b, ha, hb, heU⟩ := bigOmega_eq_two_factors (by omega) hOu
  have hpar := primeFactorSum_odd_parity huo
  have heven : primeFactorSum v % 2 = 0 := by omega
  obtain ⟨r, s, hr, hs, heV⟩ := even_omega_four_even_sum_shape hv hve hOv heven
  have hSU : primeFactorSum u = a + b := by
    rw [heU, primeFactorSum_mul ha.ne_zero hb.ne_zero, primeFactorSum_prime ha, primeFactorSum_prime hb]
  have hS4 : primeFactorSum 4 = 4 := by simpa using primeFactorSum_prime_pow Nat.prime_two 2
  have hSV : primeFactorSum v = 4 + r + s := by
    rw [heV, primeFactorSum_mul (mul_ne_zero (by norm_num) hr.ne_zero) hs.ne_zero,
      primeFactorSum_mul (by norm_num) hr.ne_zero, hS4,
      primeFactorSum_prime hr, primeFactorSum_prime hs]
  have hro := hr.eq_two_or_odd
  have hso := hs.eq_two_or_odd
  have hcases : (r = 2 ∧ s = 2) ∨ (r % 2 = 1 ∧ s % 2 = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | hrs
  · omega
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hs3 : 3 ≤ s := by have := hs.two_le; omega
  have h3p : 3 < u + v := by nlinarith [Nat.mul_le_mul ha.two_le hb.two_le]
  rcases three_dvd_adjacent_prime_sum hp h3p rfl hadj with hdu | hdv
  · have hd' : 3 ∣ a * b := by simpa [heU] using hdu
    have hbound := four_odd_factor_gap hr3 hs3
    rcases Nat.prime_three.dvd_mul.mp hd' with hda | hdb
    · have ha3 : a = 3 := ((ha.eq_one_or_self_of_dvd 3 hda).resolve_left (by norm_num)).symm
      subst a
      exfalso
      rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hbound, hadj]
    · have hb3 : b = 3 := ((hb.eq_one_or_self_of_dvd 3 hdb).resolve_left (by norm_num)).symm
      subst b
      exfalso
      rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hbound, hadj]
  · have hnu : ¬ 3 ∣ u := adjacent_not_common_dvd (by norm_num : 1 < 3) (by omega) hdv
    have ha5 : 5 ≤ a := prime_five_le_of_dvd_odd ha ⟨b, heU⟩ huo hnu
    have hb5 : 5 ≤ b := prime_five_le_of_dvd_odd hb ⟨a, by rw [heU]; ring⟩ huo hnu
    have hd' : 3 ∣ r ∨ 3 ∣ s := by
      have hh : 3 ∣ 4 * r * s := by simpa [heV] using hdv
      simpa [Nat.prime_three.dvd_mul] using hh
    rcases hd' with hdr | hds
    · have hr' : r = 3 := ((hr.eq_one_or_self_of_dvd 3 hdr).resolve_left (by norm_num)).symm
      subst r
      have hl : a * b + 83 ≤ 12 * (a + b) := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hh : 12 * (a + b) ≤ a * b + 85 := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hbound := low_pair_twelve_bound ha5 hb5 hl hh
      rw [← heU] at hbound
      omega
    · have hs' : s = 3 := ((hs.eq_one_or_self_of_dvd 3 hds).resolve_left (by norm_num)).symm
      subst s
      have hl : a * b + 83 ≤ 12 * (a + b) := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hh : 12 * (a + b) ≤ a * b + 85 := by
        rcases hadj with hadj | hadj <;> nlinarith only [heU, heV, hSU, hSV, hsum, hadj]
      have hbound := low_pair_twelve_bound ha5 hb5 hl hh
      rw [← heU] at hbound
      omega

/-- Adjacent equal sums cannot have half-neighbor count pattern (3,3). -/
theorem sumPair_three_three_impossible {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huo : u % 2 = 1) (hve : v % 2 = 0)
    (hadj : u + 1 = v ∨ v + 1 = u) (hsum : primeFactorSum u = primeFactorSum v)
    (hOu : bigOmega u = 3) (hOv : bigOmega v = 3) : False := by
  obtain ⟨a, b, c, ha, hb, hc, heU⟩ := bigOmega_eq_three_factors (by omega) hOu
  obtain ⟨r, s, hr, hs, heV⟩ := even_omega_three_shape hv hve hOv
  have hSU : primeFactorSum u = a + b + c := by
    rw [heU, primeFactorSum_mul (mul_ne_zero ha.ne_zero hb.ne_zero) hc.ne_zero,
      primeFactorSum_mul ha.ne_zero hb.ne_zero, primeFactorSum_prime ha,
      primeFactorSum_prime hb, primeFactorSum_prime hc]
  have hSV : primeFactorSum v = 2 + r + s := by
    rw [heV, primeFactorSum_mul (mul_ne_zero (by norm_num) hr.ne_zero) hs.ne_zero,
      primeFactorSum_mul (by norm_num) hr.ne_zero, primeFactorSum_prime Nat.prime_two,
      primeFactorSum_prime hr, primeFactorSum_prime hs]
  have ha3 : 3 ≤ a := prime_three_le_of_dvd_odd ha
    (by refine ⟨b * c, ?_⟩; rw [heU]; ring) huo
  have hb3 : 3 ≤ b := prime_three_le_of_dvd_odd hb
    (by refine ⟨a * c, ?_⟩; rw [heU]; ring) huo
  have hc3 : 3 ≤ c := prime_three_le_of_dvd_odd hc
    (by refine ⟨a * b, ?_⟩; rw [heU]; ring) huo
  have hbound := triple_factor_gap_bound ha3 hb3 hc3
  have hpar := primeFactorSum_odd_parity huo
  have hro := hr.eq_two_or_odd
  have hso := hs.eq_two_or_odd
  have hcases : r = 2 ∨ s = 2 := by omega
  rcases hcases with rfl | rfl <;>
    rcases hadj with hadj | hadj <;>
    nlinarith only [heU, heV, hSU, hSV, hsum, hbound, hadj]

/-- Universal size bound: no restriction on the size of the original input. -/
theorem sumBalanced_low_count_bound {p : ℕ} (h : IsPrimeFactorSumBalancedPrime p)
    (hT : omegaSum p ≤ 8) : p < 2000 := by
  obtain ⟨u, v, hu, hv, huo, hve, hcenter, hadj, hsum, htotal⟩ := sumBalanced_prime_halves h
  by_cases hu1 : u = 1
  · omega
  by_cases hv1 : v = 1
  · omega
  by_cases hup : u.Prime
  · have hb := prime_consecutive_sum_bound hup hv hadj hsum
    omega
  by_cases hvp : v.Prime
  · have hb := prime_consecutive_sum_bound hvp hu (by omega) hsum.symm
    omega
  have huO2 : 2 ≤ bigOmega u := by
    have h0 : bigOmega u ≠ 0 := by
      intro hz
      have := (bigOmega_eq_zero_iff u).mp hz
      omega
    have h1 : bigOmega u ≠ 1 := fun hh => hup ((bigOmega_eq_one_iff (by omega)).mp hh)
    omega
  have hvO2 : 2 ≤ bigOmega v := by
    have h0 : bigOmega v ≠ 0 := by
      intro hz
      have := (bigOmega_eq_zero_iff v).mp hz
      omega
    have h1 : bigOmega v ≠ 1 := fun hh => hvp ((bigOmega_eq_one_iff (by omega)).mp hh)
    omega
  have hpUV : (u + v).Prime := by simpa [hcenter] using h.1
  by_cases hv3 : 3 ≤ bigOmega v
  · have hcases : (bigOmega u = 2 ∧ bigOmega v = 3) ∨
        (bigOmega u = 2 ∧ bigOmega v = 4) ∨ (bigOmega u = 3 ∧ bigOmega v = 3) := by omega
    rw [hcenter]
    rcases hcases with ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩
    · exact sumPair_two_three_bound hu hv huo hve hpUV hadj hsum hU hV
    · exact sumPair_two_four_bound hu hv huo hve hpUV hadj hsum hU hV
    · exact (sumPair_three_three_impossible hu hv huo hve hadj hsum hU hV).elim
  · have hv2 : bigOmega v = 2 := by omega
    obtain ⟨r, hr, her⟩ := even_omega_two_shape hv hve hv2
    have hSV : primeFactorSum v = 2 + r := by
      rw [her, primeFactorSum_mul (by norm_num) hr.ne_zero,
        primeFactorSum_prime Nat.prime_two, primeFactorSum_prime hr]
    have hbound := primeFactorSum_odd_composite_bound (by omega : 1 < u) huo hup
    rw [hsum, hSV] at hbound
    omega

/-- Complete low-total-count classification for sum-balanced primes. -/
theorem sumBalanced_total_le_eight_iff (p : ℕ) :
    (IsPrimeFactorSumBalancedPrime p ∧ omegaSum p ≤ 8) ↔ p = 11 ∨ p = 17 ∨ p = 31 := by
  constructor
  · rintro ⟨hp, ht⟩
    have hb := sumBalanced_low_count_bound hp ht
    exact (small_sum_balanced_low_count ⟨p, hb⟩).mp ⟨hp.1, hp.2, ht⟩
  · intro hp
    have hb : p < 2000 := by omega
    have hh := (small_sum_balanced_low_count ⟨p, hb⟩).mpr hp
    exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩

theorem sumBalanced_total_ge_nine {p : ℕ} (h : IsPrimeFactorSumBalancedPrime p)
    (h11 : p ≠ 11) (h17 : p ≠ 17) (h31 : p ≠ 31) : 9 ≤ omegaSum p := by
  by_contra! ht
  have hh := (sumBalanced_total_le_eight_iff p).mp ⟨h, by omega⟩
  omega

/-- Every infinite fixed-total-count stratum has total count at least nine. -/
theorem infinite_sumBalanced_level_ge_nine {k : ℕ}
    (h : Set.Infinite {p : ℕ | IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = k}) : 9 ≤ k := by
  by_contra! hk
  have hf : ({11, 17, 31} : Set ℕ).Finite := by simp
  apply h
  apply hf.subset
  intro p hp
  change IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = k at hp
  have hh := (sumBalanced_total_le_eight_iff p).mp ⟨hp.1, by omega⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh

/-- The explicit center polynomial is strictly increasing on natural parameters. -/
theorem sumFamilyCenter_strictMono : StrictMono sumFamilyCenter := by
  intro a b hab
  have hab' : a ≤ b := Nat.le_of_lt hab
  have h2 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hab' 2
  have h3 : a ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hab' 3
  have h1 : 8160 * a < 8160 * b := Nat.mul_lt_mul_of_pos_left hab (by norm_num)
  simp only [sumFamilyCenter]
  omega

/-- An explicit infinitude hypothesis is transported, not asserted or axiomatized. -/
theorem infinite_sumFamily_implies_level_nine
    (h : Set.Infinite {t : ℕ | SumFamilyPrimeValues t}) :
    Set.Infinite {p : ℕ | IsPrimeFactorSumBalancedPrime p ∧ omegaSum p = 9} := by
  have hi := h.image sumFamilyCenter_strictMono.injective.injOn
  apply hi.mono
  rintro p ⟨t, ht, rfl⟩
  exact ⟨sumFamily_five_primes ht, sumFamily_omegaSum_eq_nine ht⟩

end OmegaBalance
