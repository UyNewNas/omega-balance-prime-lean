import OmegaBalance.FactorSum

/-! Elementary inequalities, factor-list shapes, and parity for the sum statistic. -/

namespace OmegaBalance

theorem factorList_prod_pos {l : List ℕ} (h : ∀ a ∈ l, 2 ≤ a) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ht : ∀ b ∈ l, 2 ≤ b := fun b hb => h b (by simp [hb])
    simpa using Nat.mul_pos (by omega : 0 < a) (ih ht)

theorem factorList_two_le_prod {l : List ℕ} (hn : l ≠ [])
    (h : ∀ a ∈ l, 2 ≤ a) : 2 ≤ l.prod := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons a l =>
    have ha := h a (by simp)
    have ht : ∀ b ∈ l, 2 ≤ b := fun b hb => h b (by simp [hb])
    have hh := factorList_prod_pos ht
    simp only [List.prod_cons]
    nlinarith [Nat.mul_le_mul ha (show 1 ≤ l.prod by omega)]

theorem factorList_sum_le_prod {l : List ℕ} (h : ∀ a ∈ l, 2 ≤ a) :
    l.sum ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ht : ∀ b ∈ l, 2 ≤ b := fun b hb => h b (by simp [hb])
    have hs := ih ht
    by_cases hn : l = []
    · simp [hn]
    · have hp := factorList_two_le_prod hn ht
      simp only [List.sum_cons, List.prod_cons]
      nlinarith [Nat.mul_le_mul_right l.prod ha, Nat.mul_le_mul_left a hp]

theorem primeFactorSum_le (n : ℕ) : primeFactorSum n ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  have h := factorList_sum_le_prod (l := n.primeFactorsList)
    (fun a ha => (Nat.prime_of_mem_primeFactorsList ha).two_le)
  simpa [primeFactorSum, Nat.prod_primeFactorsList hn] using h

/-- At positive n equality characterizes primes, with the single exception 4. -/
theorem primeFactorSum_eq_self_iff {n : ℕ} (hn : 0 < n) :
    primeFactorSum n = n ↔ n.Prime ∨ n = 4 := by
  constructor
  · intro he
    by_cases hp : n.Prime
    · exact Or.inl hp
    right
    have hn1 : n ≠ 1 := by intro h; simp [h] at he
    have hn2 : 2 ≤ n := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hn2).mp hp
    have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> simp_all
    have hb2 : 2 ≤ b := by
      by_contra! h
      interval_cases b <;> simp_all
    have hs : n ≤ a + b := by
      rw [← he, ← hab, primeFactorSum_mul (by omega) (by omega)]
      exact Nat.add_le_add (primeFactorSum_le a) (primeFactorSum_le b)
    have ha' : a = 2 := by
      by_contra h
      have h3 : 3 ≤ a := by omega
      nlinarith [Nat.mul_le_mul_right b h3, Nat.mul_le_mul_left a hb2]
    have hb' : b = 2 := by
      subst a
      nlinarith
    simpa [ha', hb'] using hab.symm
  · rintro (hp | rfl)
    · exact primeFactorSum_prime hp
    · simpa using primeFactorSum_prime_pow Nat.prime_two 2

theorem primeFactorDefect_nonneg (n : ℕ) : 0 ≤ primeFactorDefect n := by
  have h := primeFactorSum_le n
  unfold primeFactorDefect
  omega

theorem primeFactorDefect_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    primeFactorDefect n = 0 ↔ n.Prime ∨ n = 4 := by
  have he : primeFactorDefect n = 0 ↔ primeFactorSum n = n := by
    unfold primeFactorDefect
    omega
  exact he.trans (primeFactorSum_eq_self_iff hn)

/-- An odd composite obeys the stronger bound 3*S(n) <= n+9. -/
theorem primeFactorSum_odd_composite_bound {n : ℕ}
    (hn : 1 < n) (hodd : n % 2 = 1) (hc : ¬ n.Prime) :
    3 * primeFactorSum n ≤ n + 9 := by
  obtain ⟨a, b, ha, hb, hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ n)).mp hc
  have ha2 : 2 ≤ a := by
    by_contra! h
    interval_cases a <;> simp_all
  have hb2 : 2 ≤ b := by
    by_contra! h
    interval_cases b <;> simp_all
  have hao : a % 2 = 1 := by
    by_contra hne
    have hz : a % 2 = 0 := by omega
    have hz' : n % 2 = 0 := by rw [← hab, Nat.mul_mod, hz]; simp
    omega
  have hbo : b % 2 = 1 := by
    by_contra hne
    have hz : b % 2 = 0 := by omega
    have hz' : n % 2 = 0 := by rw [← hab, Nat.mul_mod, hz]; simp
    omega
  have ha3 : 3 ≤ a := by omega
  have hb3 : 3 ≤ b := by omega
  have hs : primeFactorSum n ≤ a + b := by
    rw [← hab, primeFactorSum_mul (by omega) (by omega)]
    exact Nat.add_le_add (primeFactorSum_le a) (primeFactorSum_le b)
  have hmul : 3 * (a + b) ≤ a * b + 9 := by
    obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le ha3
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hb3
    nlinarith [Nat.zero_le (x * y)]
  omega

theorem bigOmega_eq_zero_iff (n : ℕ) : bigOmega n = 0 ↔ n = 0 ∨ n = 1 := by
  simp [bigOmega]

theorem bigOmega_eq_one_iff {n : ℕ} (hn : n ≠ 0) : bigOmega n = 1 ↔ n.Prime := by
  constructor
  · intro h
    have he := Nat.prod_primeFactorsList hn
    cases hl : n.primeFactorsList with
    | nil => simp [bigOmega, hl] at h
    | cons a l =>
      have hz : l = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [bigOmega, hl, List.length_cons] at h
        omega
      subst l
      have hp : a.Prime := Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl])
      simp only [hl, List.prod_cons, List.prod_nil, mul_one] at he
      simpa [he] using hp
  · exact bigOmega_prime

theorem bigOmega_eq_two_factors {n : ℕ} (hn : n ≠ 0) (h : bigOmega n = 2) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ n = a * b := by
  have he := Nat.prod_primeFactorsList hn
  cases hl : n.primeFactorsList with
  | nil => simp [bigOmega, hl] at h
  | cons a l =>
    cases l with
    | nil => simp [bigOmega, hl] at h
    | cons b l =>
      have hz : l = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [bigOmega, hl, List.length_cons] at h
        omega
      subst l
      refine ⟨a, b, Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
        Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]), ?_⟩
      simpa [hl] using he.symm

theorem bigOmega_eq_three_factors {n : ℕ} (hn : n ≠ 0) (h : bigOmega n = 3) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ n = a * b * c := by
  have he := Nat.prod_primeFactorsList hn
  cases hl : n.primeFactorsList with
  | nil => simp [bigOmega, hl] at h
  | cons a l =>
    cases l with
    | nil => simp [bigOmega, hl] at h
    | cons b l =>
      cases l with
      | nil => simp [bigOmega, hl] at h
      | cons c l =>
        have hz : l = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [bigOmega, hl, List.length_cons] at h
          omega
        subst l
        refine ⟨a, b, c, Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
          Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
          Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]), ?_⟩
        simpa [hl, mul_assoc] using he.symm

theorem bigOmega_eq_four_factors {n : ℕ} (hn : n ≠ 0) (h : bigOmega n = 4) :
    ∃ a b c d : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ n = a * b * c * d := by
  have he := Nat.prod_primeFactorsList hn
  cases hl : n.primeFactorsList with
  | nil => simp [bigOmega, hl] at h
  | cons a l =>
    cases l with
    | nil => simp [bigOmega, hl] at h
    | cons b l =>
      cases l with
      | nil => simp [bigOmega, hl] at h
      | cons c l =>
        cases l with
        | nil => simp [bigOmega, hl] at h
        | cons d l =>
          have hz : l = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [bigOmega, hl, List.length_cons] at h
            omega
          subst l
          refine ⟨a, b, c, d, Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
            Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
            Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]),
            Nat.prime_of_mem_primeFactorsList (n := n) (by simp [hl]), ?_⟩
          simpa [hl, mul_assoc] using he.symm

/-- Parity counts the odd prime factors. -/
theorem factorList_sum_twos_parity {l : List ℕ} (h : ∀ a ∈ l, a.Prime) :
    (l.sum + l.count 2) % 2 = l.length % 2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hp := h a (by simp)
    have ht : ∀ b ∈ l, b.Prime := fun b hb => h b (by simp [hb])
    have hh := ih ht
    by_cases ha : a = 2
    · subst a
      simp only [List.sum_cons, List.length_cons, List.count_cons_self]
      omega
    · have hc : (a :: l).count 2 = l.count 2 := by simp [ha]
      have ho := hp.mod_two_eq_one_iff_ne_two.mpr ha
      simp only [List.sum_cons, List.length_cons, hc]
      omega

theorem primeFactorSum_parity (n : ℕ) :
    (primeFactorSum n + valuation 2 n) % 2 = bigOmega n % 2 := by
  simpa only [primeFactorSum, bigOmega, Nat.primeFactorsList_count_eq, valuation] using
    factorList_sum_twos_parity (l := n.primeFactorsList)
      (fun a ha => Nat.prime_of_mem_primeFactorsList ha)

theorem primeFactorSum_odd_parity {n : ℕ} (hn : n % 2 = 1) :
    primeFactorSum n % 2 = bigOmega n % 2 := by
  have hz : valuation 2 n = 0 := valuation_eq_zero_of_not_dvd (by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega)
  simpa [hz] using primeFactorSum_parity n

theorem sumBalanced_count_valuation_parity {n : ℕ} (h : IsPrimeFactorSumBalanced n) :
    omegaDiff n % 2 = valuationDiff 2 n % 2 := by
  have hl := primeFactorSum_parity (n - 1)
  have hr := primeFactorSum_parity (n + 1)
  unfold IsPrimeFactorSumBalanced at h
  unfold omegaDiff valuationDiff neighborDiff
  omega

theorem valuation_eq_of_pow_dvd {q n k : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (hl : q ^ k ∣ n) (hr : ¬ q ^ (k + 1) ∣ n) : valuation q n = k := by
  have hlo := (hq.pow_dvd_iff_le_factorization hn).mp hl
  have hhi : ¬ k + 1 ≤ n.factorization q := by
    intro hh
    exact hr ((hq.pow_dvd_iff_le_factorization hn).mpr hh)
  unfold valuation
  omega

/-- Simultaneous balance forces residue one or seven modulo eight. -/
theorem doubleBalanced_mod_eight {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  have h2 : 2 < p := by
    have hp := h.1.two_le
    by_contra! hn
    have he : p = 2 := by omega
    have hb := h.2.1
    simp [IsPrimeFactorSumBalanced, he, primeFactorSum_prime Nat.prime_three] at hb
  have ho := prime_mod_two_eq_one h.1 h2
  have hp1 : p - 1 ≠ 0 := by omega
  have hp2 : p + 1 ≠ 0 := by omega
  have hl := primeFactorSum_parity (p - 1)
  have hr := primeFactorSum_parity (p + 1)
  have hs := h.2.1
  unfold IsPrimeFactorSumBalanced at hs
  rw [h.2.2.1] at hl
  rw [h.2.2.2] at hr
  by_contra! hh
  have hc : p % 8 = 3 ∨ p % 8 = 5 := by omega
  rcases hc with hc | hc
  · have hvl : valuation 2 (p - 1) = 1 := valuation_eq_of_pow_dvd Nat.prime_two hp1
      (by norm_num; apply Nat.dvd_iff_mod_eq_zero.mpr; omega)
      (by norm_num; intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)
    have hvr : valuation 2 (p + 1) = 2 := valuation_eq_of_pow_dvd Nat.prime_two hp2
      (by norm_num; apply Nat.dvd_iff_mod_eq_zero.mpr; omega)
      (by norm_num; intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)
    omega
  · have hvl : valuation 2 (p - 1) = 2 := valuation_eq_of_pow_dvd Nat.prime_two hp1
      (by norm_num; apply Nat.dvd_iff_mod_eq_zero.mpr; omega)
      (by norm_num; intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)
    have hvr : valuation 2 (p + 1) = 1 := valuation_eq_of_pow_dvd Nat.prime_two hp2
      (by norm_num; apply Nat.dvd_iff_mod_eq_zero.mpr; omega)
      (by norm_num; intro hd; have := Nat.mod_eq_zero_of_dvd hd; omega)
    omega

end OmegaBalance
