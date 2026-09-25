import OmegaBalance.FactorSumStructure
import OmegaBalance.FactorSumSmallCertificates

/-! Preparatory lemmas for the unrestricted low-count classification. -/

namespace OmegaBalance

theorem sumBalanced_prime_halves {p : ℕ} (h : IsPrimeFactorSumBalancedPrime p) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u % 2 = 1 ∧ v % 2 = 0 ∧
      p = u + v ∧ (u + 1 = v ∨ v + 1 = u) ∧
      primeFactorSum u = primeFactorSum v ∧
      omegaSum p = 2 + bigOmega u + bigOmega v := by
  have hp2 : 2 < p := by
    have hl := h.1.two_le
    by_contra! hh
    have he : p = 2 := by omega
    have hs := h.2
    simp [IsPrimeFactorSumBalanced, he, primeFactorSum_prime Nat.prime_three] at hs
  have ho := prime_mod_two_eq_one h.1 hp2
  let a := (p - 1) / 2
  let b := (p + 1) / 2
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := by dsimp [b]; omega
  have heL : p - 1 = 2 * a := by dsimp [a]; omega
  have heR : p + 1 = 2 * b := by dsimp [b]; omega
  have hab : a + 1 = b := by dsimp [a, b]; omega
  have hep : p = a + b := by omega
  have hs := h.2
  change primeFactorSum (p - 1) = primeFactorSum (p + 1) at hs
  rw [heL, heR, primeFactorSum_mul (by omega) (by omega),
    primeFactorSum_mul (by omega) (by omega)] at hs
  have hO : omegaSum p = 2 + bigOmega a + bigOmega b := by
    unfold omegaSum
    rw [heL, heR, bigOmega_mul (by omega) (by omega),
      bigOmega_mul (by omega) (by omega), bigOmega_prime Nat.prime_two]
    omega
  by_cases hao : a % 2 = 1
  · exact ⟨a, b, ha, hb, hao, by omega, hep, Or.inl hab, by omega, hO⟩
  · exact ⟨b, a, hb, ha, by omega, by omega, by omega,
      Or.inr hab, by omega, by omega⟩

theorem even_factor_sum_split {v : ℕ} (hv : 0 < v) (he : v % 2 = 0) :
    ∃ w : ℕ, 0 < w ∧ v = 2 * w ∧
      bigOmega v = 1 + bigOmega w ∧ primeFactorSum v = 2 + primeFactorSum w := by
  obtain ⟨w, hw⟩ := Nat.dvd_iff_mod_eq_zero.mpr he
  have hp : 0 < w := by omega
  refine ⟨w, hp, hw, ?_, ?_⟩
  · rw [hw, bigOmega_mul (by omega) (by omega), bigOmega_prime Nat.prime_two]
  · rw [hw, primeFactorSum_mul (by omega) (by omega), primeFactorSum_prime Nat.prime_two]

theorem prime_consecutive_sum_bound {q e : ℕ} (hq : q.Prime) (he : 0 < e)
    (hadj : q + 1 = e ∨ e + 1 = q)
    (hs : primeFactorSum q = primeFactorSum e) : q ≤ 5 := by
  by_contra! hq5
  have hqo := prime_mod_two_eq_one hq (by omega)
  have heo : e % 2 = 0 := by omega
  obtain ⟨w, hw, hew, _, hsum⟩ := even_factor_sum_split he heo
  have hle := primeFactorSum_le w
  rw [primeFactorSum_prime hq] at hs
  omega

/-- The only consecutive equal-S pair containing a prime is {5,6}, with the prime equal to 5. -/
theorem prime_consecutive_sum_eq_five_six {q e : ℕ} (hq : q.Prime) (he : 0 < e)
    (hadj : q + 1 = e ∨ e + 1 = q)
    (hs : primeFactorSum q = primeFactorSum e) : q = 5 ∧ e = 6 := by
  have hq2 := hq.two_le
  have hq5 := prime_consecutive_sum_bound hq he hadj hs
  have hq_cases : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq_cases with rfl | rfl | rfl | rfl
  · have he_cases : e = 1 ∨ e = 3 := by omega
    rcases he_cases with rfl | rfl <;> norm_num [primeFactorSum] at hs
  · have he_cases : e = 2 ∨ e = 4 := by omega
    rcases he_cases with rfl | rfl <;> norm_num [primeFactorSum] at hs
  · norm_num at hq
  · have he_cases : e = 4 ∨ e = 6 := by omega
    rcases he_cases with rfl | rfl
    · norm_num [primeFactorSum] at hs
    · exact ⟨rfl, rfl⟩

/-- Apart from center 11, neither half-neighbor of an S-balanced prime is prime. -/
theorem sumBalanced_halves_nonprime_of_ne_eleven {p : ℕ}
    (h : IsPrimeFactorSumBalancedPrime p) (h11 : p ≠ 11) :
    ¬ ((p - 1) / 2).Prime ∧ ¬ ((p + 1) / 2).Prime := by
  have hp2 : 2 < p := by
    have hp := h.1.two_le
    by_contra! hn
    have heq : p = 2 := by omega
    have hs := h.2
    simp [IsPrimeFactorSumBalanced, heq, primeFactorSum_prime Nat.prime_three] at hs
  have hodd := prime_mod_two_eq_one h.1 hp2
  have hsum := (primeFactorSumBalanced_iff_half (by omega) hodd).mp h.2
  have hadj : (p - 1) / 2 + 1 = (p + 1) / 2 := by omega
  constructor
  · intro hleft
    have hh := prime_consecutive_sum_eq_five_six hleft (by omega) (Or.inl hadj) hsum
    exact h11 (by omega)
  · intro hright
    have hh := prime_consecutive_sum_eq_five_six hright (by omega) (Or.inr hadj) hsum.symm
    exact h11 (by omega)

theorem even_omega_two_shape {v : ℕ} (hv : 0 < v) (he : v % 2 = 0)
    (hO : bigOmega v = 2) : ∃ r : ℕ, r.Prime ∧ v = 2 * r := by
  obtain ⟨w, hw, hew, how, _⟩ := even_factor_sum_split hv he
  have h1 : bigOmega w = 1 := by omega
  exact ⟨w, (bigOmega_eq_one_iff (by omega)).mp h1, hew⟩

theorem even_omega_three_shape {v : ℕ} (hv : 0 < v) (he : v % 2 = 0)
    (hO : bigOmega v = 3) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ v = 2 * r * s := by
  obtain ⟨w, hw, hew, how, _⟩ := even_factor_sum_split hv he
  have h2 : bigOmega w = 2 := by omega
  obtain ⟨r, s, hr, hs, hrs⟩ := bigOmega_eq_two_factors (by omega) h2
  exact ⟨r, s, hr, hs, by rw [hew, hrs]; ring⟩

theorem even_omega_four_even_sum_shape {v : ℕ} (hv : 0 < v) (he : v % 2 = 0)
    (hO : bigOmega v = 4) (hS : primeFactorSum v % 2 = 0) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ v = 4 * r * s := by
  obtain ⟨w, hw, hew, how, hsw⟩ := even_factor_sum_split hv he
  have hpar := primeFactorSum_parity w
  have hv2 : 0 < valuation 2 w := by omega
  have hdw : 2 ∣ w := (valuation_pos_iff_dvd Nat.prime_two (by omega)).mp hv2
  obtain ⟨z, hz, hez, hoz, _⟩ := even_factor_sum_split hw (Nat.mod_eq_zero_of_dvd hdw)
  have h2 : bigOmega z = 2 := by omega
  obtain ⟨r, s, hr, hs, hrs⟩ := bigOmega_eq_two_factors (by omega) h2
  exact ⟨r, s, hr, hs, by rw [hew, hez, hrs]; ring⟩

theorem three_dvd_adjacent_prime_sum {u v p : ℕ} (hp : p.Prime) (h3 : 3 < p)
    (hep : p = u + v) (hadj : u + 1 = v ∨ v + 1 = u) : 3 ∣ u ∨ 3 ∣ v := by
  by_contra! hn
  have hu : u % 3 ≠ 0 := fun hh => hn.1 (Nat.dvd_iff_mod_eq_zero.mpr hh)
  have hv : v % 3 ≠ 0 := fun hh => hn.2 (Nat.dvd_iff_mod_eq_zero.mpr hh)
  have hu_lt : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hv_lt : v % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hu_cases : u % 3 = 1 ∨ u % 3 = 2 := by omega
  have hv_cases : v % 3 = 1 ∨ v % 3 = 2 := by omega
  have huv : u % 3 + v % 3 = 3 := by
    rcases hu_cases with hu1 | hu2 <;> rcases hv_cases with hv1 | hv2
    · exfalso
      rcases hadj with hadd | hadd
      · have heq := congrArg (fun z : ℕ => z % 3) hadd
        rw [Nat.add_mod] at heq
        norm_num [hu1, hv1] at heq
      · have heq := congrArg (fun z : ℕ => z % 3) hadd
        rw [Nat.add_mod] at heq
        norm_num [hu1, hv1] at heq
    · omega
    · omega
    · exfalso
      rcases hadj with hadd | hadd
      · have heq := congrArg (fun z : ℕ => z % 3) hadd
        rw [Nat.add_mod] at heq
        norm_num [hu2, hv2] at heq
      · have heq := congrArg (fun z : ℕ => z % 3) hadd
        rw [Nat.add_mod] at heq
        norm_num [hu2, hv2] at heq
  have hm : p % 3 = 0 := by
    calc
      p % 3 = (u % 3 + v % 3) % 3 := by rw [hep, Nat.add_mod]
      _ = 0 := by norm_num [huv]
  exact not_three_dvd_prime hp h3 (Nat.dvd_iff_mod_eq_zero.mpr hm)

theorem adjacent_not_common_dvd {u v q : ℕ} (hq : 1 < q)
    (hadj : u + 1 = v ∨ v + 1 = u) (hu : q ∣ u) : ¬ q ∣ v := by
  intro hv
  have hu0 := Nat.mod_eq_zero_of_dvd hu
  have hv0 := Nat.mod_eq_zero_of_dvd hv
  have h1 : 1 % q = 1 := Nat.mod_eq_of_lt hq
  rcases hadj with hadj | hadj
  all_goals
    have hh := congrArg (fun n : ℕ => n % q) hadj
    simp [Nat.add_mod, hu0, hv0, h1] at hh

theorem two_odd_factor_gap {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    3 * (a + b) ≤ 2 * a * b := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
  ring_nf
  omega

theorem four_odd_factor_gap {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    3 * (a + b) + 18 ≤ 4 * a * b := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
  ring_nf
  omega

theorem low_pair_six_bound {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b)
    (hl : a * b + 29 ≤ 6 * (a + b)) (hr : 6 * (a + b) ≤ a * b + 31) :
    a * b ≤ 91 := by
  have ha7 : 7 ≤ a := by
    by_contra! h
    interval_cases a <;> omega
  have hb7 : 7 ≤ b := by
    by_contra! h
    interval_cases b <;> omega
  have hprod : 7 * (a + b) ≤ a * b + 49 := by
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha7
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb7
    ring_nf
    omega
  omega

theorem low_pair_twelve_bound {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b)
    (hl : a * b + 83 ≤ 12 * (a + b)) (hr : 12 * (a + b) ≤ a * b + 85) :
    a * b ≤ 949 := by
  have ha13 : 13 ≤ a := by
    by_contra! h
    interval_cases a <;> omega
  have hb13 : 13 ≤ b := by
    by_contra! h
    interval_cases b <;> omega
  have hprod : 13 * (a + b) ≤ a * b + 169 := by
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha13
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb13
    ring_nf
    omega
  omega

/-- Finite classification derived from verified factorization certificates. -/
theorem small_sum_balanced_low_count :
    ∀ p : Fin 2000,
      (p.val.Prime ∧ primeFactorSum (p.val - 1) = primeFactorSum (p.val + 1) ∧
        bigOmega (p.val - 1) + bigOmega (p.val + 1) ≤ 8) ↔
      p.val = 11 ∨ p.val = 17 ∨ p.val = 31 := by
  intro p
  have hclass (hp : p.val.Prime) :
      (primeFactorSum (p.val - 1) = primeFactorSum (p.val + 1) ∧
        bigOmega (p.val - 1) + bigOmega (p.val + 1) ≤ 8) ↔
      p.val = 11 ∨ p.val = 17 ∨ p.val = 31 := by
    obtain ⟨row, hm, he⟩ := List.mem_map.mp (smallSumCertificates_cover p hp)
    obtain ⟨hL, hR, hPL, hPR, ht⟩ := smallSumCertificates_valid row hm
    have hl : row.2.1.prod = p.val - 1 := by simpa only [he] using hL
    have hr : row.2.2.prod = p.val + 1 := by simpa only [he] using hR
    rw [primeFactorSum_of_factors hl hPL, primeFactorSum_of_factors hr hPR,
      bigOmega_of_factors hl hPL, bigOmega_of_factors hr hPR]
    simpa only [he] using ht
  constructor
  · rintro ⟨hp, hs, ho⟩
    exact (hclass hp).mp ⟨hs, ho⟩
  · intro h
    have hp : p.val.Prime := by
      rcases h with he | he | he <;> rw [he] <;> norm_num
    exact ⟨hp, (hclass hp).mpr h⟩

end OmegaBalance
