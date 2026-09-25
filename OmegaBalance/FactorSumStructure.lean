import OmegaBalance.FactorSumArithmetic
import OmegaBalance.F3

/-! Structural restrictions and constructive certificates for double balance. -/

namespace OmegaBalance

/-- A prime dividing an odd integer is at least three. -/
theorem prime_three_le_of_dvd_odd {q n : ℕ} (hq : q.Prime)
    (hd : q ∣ n) (hn : n % 2 = 1) : 3 ≤ q := by
  have h2 := hq.two_le
  by_contra! h
  have he : q = 2 := by omega
  rw [he] at hd
  have := Nat.mod_eq_zero_of_dvd hd
  omega

/-- A prime dividing an odd integer not divisible by three is at least five. -/
theorem prime_five_le_of_dvd_odd {q n : ℕ} (hq : q.Prime)
    (hd : q ∣ n) (hn : n % 2 = 1) (h3 : ¬ 3 ∣ n) : 5 ≤ q := by
  have hl := prime_three_le_of_dvd_odd hq hd hn
  have hq3 : q ≠ 3 := by intro h; subst q; exact h3 hd
  exact hq.five_le_of_ne_two_of_ne_three (by omega) hq3

/-- Split the neighbors as 2*u and 8*v, with u odd. -/
theorem doubleBalanced_split {p k : ℕ} (h : IsDoubleBalancedPrime p k) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u % 2 = 1 ∧ p = u + 4 * v ∧
      (u + 1 = 4 * v ∨ 4 * v + 1 = u) ∧
      primeFactorSum u = primeFactorSum v + 4 ∧
      bigOmega u + 1 = k ∧ bigOmega v + 3 = k := by
  have hp := h.1.two_le
  have hs := h.2.1
  change primeFactorSum (p - 1) = primeFactorSum (p + 1) at hs
  have hl := h.2.2.1
  have hr := h.2.2.2
  have hS8 : primeFactorSum 8 = 6 := by
    simpa using primeFactorSum_prime_pow Nat.prime_two 3
  have hO8 : bigOmega 8 = 3 := by
    simpa using bigOmega_prime_pow Nat.prime_two 3
  rcases doubleBalanced_mod_eight h with hm | hm
  · let u := (p + 1) / 2
    let v := (p - 1) / 8
    have hu : 0 < u := by dsimp [u]; omega
    have hv : 0 < v := by dsimp [v]; omega
    have heL : p - 1 = 8 * v := by dsimp [v]; omega
    have heR : p + 1 = 2 * u := by dsimp [u]; omega
    rw [heL, heR, primeFactorSum_mul (by omega) (by omega),
      primeFactorSum_mul (by omega) (by omega), hS8,
      primeFactorSum_prime Nat.prime_two] at hs
    rw [heL, bigOmega_mul (by omega) (by omega), hO8] at hl
    rw [heR, bigOmega_mul (by omega) (by omega), bigOmega_prime Nat.prime_two] at hr
    refine ⟨u, v, hu, hv, ?_, ?_, Or.inr ?_, ?_, ?_, ?_⟩
    · dsimp [u]; omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · let u := (p - 1) / 2
    let v := (p + 1) / 8
    have hu : 0 < u := by dsimp [u]; omega
    have hv : 0 < v := by dsimp [v]; omega
    have heL : p - 1 = 2 * u := by dsimp [u]; omega
    have heR : p + 1 = 8 * v := by dsimp [v]; omega
    rw [heL, heR, primeFactorSum_mul (by omega) (by omega),
      primeFactorSum_mul (by omega) (by omega), hS8,
      primeFactorSum_prime Nat.prime_two] at hs
    rw [heL, bigOmega_mul (by omega) (by omega), bigOmega_prime Nat.prime_two] at hl
    rw [heR, bigOmega_mul (by omega) (by omega), hO8] at hr
    refine ⟨u, v, hu, hv, ?_, ?_, Or.inl ?_, ?_, ?_, ?_⟩
    · dsimp [u]; omega
    · omega
    · omega
    · omega
    · omega
    · omega

/-- A product of three odd primes is too large for the level-four shape. -/
theorem triple_factor_gap_bound {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    4 * (a + b + c) + 7 ≤ a * b * c + 16 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hc
  ring_nf
  omega

/-- Unconditional lower bound for the common count level. -/
theorem doubleBalanced_level_ge_five {p k : ℕ} (h : IsDoubleBalancedPrime p k) : 5 ≤ k := by
  obtain ⟨u, v, hu, hv, huo, hcenter, hadj, hsum, hOu, hOv⟩ := doubleBalanced_split h
  by_contra! hk
  have hcases : bigOmega v = 0 ∨ bigOmega v = 1 := by omega
  rcases hcases with hz | hone
  · have he : v = 1 := by
      have := (bigOmega_eq_zero_iff v).mp hz
      omega
    subst v
    have huc : u = 3 ∨ u = 5 := by omega
    rcases huc with rfl | rfl
    · norm_num [primeFactorSum_prime Nat.prime_three] at hsum
    · norm_num [primeFactorSum_prime (by norm_num : Nat.Prime 5)] at hsum
  · have hvp := (bigOmega_eq_one_iff (by omega : v ≠ 0)).mp hone
    have hou : bigOmega u = 3 := by omega
    obtain ⟨a, b, c, ha, hb, hc, he⟩ := bigOmega_eq_three_factors (by omega) hou
    have ha3 : 3 ≤ a := prime_three_le_of_dvd_odd ha
      (by refine ⟨b * c, ?_⟩; rw [he]; ring) huo
    have hb3 : 3 ≤ b := prime_three_le_of_dvd_odd hb
      (by refine ⟨a * c, ?_⟩; rw [he]; ring) huo
    have hc3 : 3 ≤ c := prime_three_le_of_dvd_odd hc
      (by refine ⟨a * b, ?_⟩; rw [he]; ring) huo
    rw [he, primeFactorSum_mul (mul_ne_zero ha.ne_zero hb.ne_zero) hc.ne_zero,
      primeFactorSum_mul ha.ne_zero hb.ne_zero, primeFactorSum_prime ha,
      primeFactorSum_prime hb, primeFactorSum_prime hc, primeFactorSum_prime hvp] at hsum
    have hbound := triple_factor_gap_bound ha3 hb3 hc3
    rw [← he] at hbound
    omega

/-- The level-five shape, expressed with an orientation disjunction. -/
def HasDoubleFiveShape (p : ℕ) : Prop :=
  ∃ b c d r s : ℕ,
    (∀ z ∈ [b, c, d, r, s], z.Prime ∧ z % 2 = 1) ∧
    ((p - 1 = 6 * b * c * d ∧ p + 1 = 8 * r * s) ∨
     (p + 1 = 6 * b * c * d ∧ p - 1 = 8 * r * s)) ∧
    r + s + 1 = b + c + d

/-- Sufficient factor certificate; the center must separately be prime. -/
theorem doubleBalanced_five_of_shape {p : ℕ} (hp : p.Prime)
    (h : HasDoubleFiveShape p) : IsDoubleBalancedPrime p 5 := by
  obtain ⟨b, c, d, r, s, hz, he, hsum⟩ := h
  have hb := (hz b (by simp)).1
  have hc := (hz c (by simp)).1
  have hd := (hz d (by simp)).1
  have hr := (hz r (by simp)).1
  have hs := (hz s (by simp)).1
  have hL : ∀ z ∈ [2, 3, b, c, d], z.Prime := by
    intro z hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hb | exact hc | exact hd | norm_num
  have hR : ∀ z ∈ [2, 2, 2, r, s], z.Prime := by
    intro z hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      first | exact hr | exact hs | norm_num
  have heL : [2, 3, b, c, d].prod = 6 * b * c * d := by
    simp only [List.prod_cons, List.prod_nil]; ring
  have heR : [2, 2, 2, r, s].prod = 8 * r * s := by
    simp only [List.prod_cons, List.prod_nil]; ring
  have hSL := primeFactorSum_of_factors heL hL
  have hSR := primeFactorSum_of_factors heR hR
  have hOL := bigOmega_of_factors heL hL
  have hOR := bigOmega_of_factors heR hR
  norm_num at hSL hSR hOL hOR
  rcases he with ⟨hl, hr'⟩ | ⟨hr', hl⟩
  · refine ⟨hp, ?_, ?_, ?_⟩
    · change primeFactorSum (p - 1) = primeFactorSum (p + 1)
      rw [hl, hr', hSL, hSR]; omega
    · rw [hl, hOL]
    · rw [hr', hOR]
  · refine ⟨hp, ?_, ?_, ?_⟩
    · change primeFactorSum (p - 1) = primeFactorSum (p + 1)
      rw [hl, hr', hSL, hSR]; omega
    · rw [hl, hOR]
    · rw [hr', hOL]

/-- The factor shape forces only two residue classes modulo 48. -/
theorem doubleFiveShape_mod_forty_eight {p : ℕ} (hp : 1 < p)
    (h : HasDoubleFiveShape p) : p % 48 = 7 ∨ p % 48 = 41 := by
  obtain ⟨b, c, d, r, s, hz, he, _⟩ := h
  have hro := (hz r (by simp)).2
  have hso := (hz s (by simp)).2
  have ho : (r * s) % 2 = 1 := by simp [Nat.mul_mod, hro, hso]
  have h16 : (8 * r * s) % 16 = 8 := by
    have hh : 8 * r * s = 8 * (r * s) := by ring
    rw [hh]
    omega
  have hd3 : 3 ∣ 6 * b * c * d := ⟨2 * b * c * d, by ring⟩
  have h3 := Nat.mod_eq_zero_of_dvd hd3
  rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rw [← hl] at h3
    rw [← hr] at h16
    omega
  · rw [← hr] at h3
    rw [← hl] at h16
    omega

/-- The precise factor shape cannot occur at both twin centers. -/
theorem doubleFiveShape_not_twins {p : ℕ} (hp : 1 < p)
    (h : HasDoubleFiveShape p) (h' : HasDoubleFiveShape (p + 2)) : False := by
  have hl := doubleFiveShape_mod_forty_eight hp h
  have hr := doubleFiveShape_mod_forty_eight (by omega) h'
  omega

/-- Four odd factors at least five give a gap far larger than one. -/
theorem quadruple_factor_gap_bound {a b c d : ℕ}
    (ha : 5 ≤ a) (hb : 5 ≤ b) (hc : 5 ≤ c) (hd : 5 ≤ d) :
    12 * (a + b + c + d) + 469 ≤ a * b * c * d + 84 := by
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hb
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hc
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le hd
  ring_nf
  omega

end OmegaBalance
