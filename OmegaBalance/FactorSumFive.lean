import OmegaBalance.FactorSumStructure
import OmegaBalance.FactorSumCofactor

/-! Necessity of the level-five factor shape and twin-prime consequences. -/

namespace OmegaBalance

set_option maxHeartbeats 2000000

/-- Every level-five double-balanced prime has the prescribed factor shape. -/
theorem doubleBalanced_five_has_shape {p : ℕ} (h : IsDoubleBalancedPrime p 5) :
    HasDoubleFiveShape p := by
  obtain ⟨u, v, hu, hv, huo, hcenter, hadj, hsum, hOu, hOv⟩ := doubleBalanced_split h
  have hou : bigOmega u = 4 := by omega
  have hov : bigOmega v = 2 := by omega
  obtain ⟨a, b, c, d, ha, hb, hc, hd, heU⟩ := bigOmega_eq_four_factors (by omega) hou
  obtain ⟨r, s, hr, hs, heV⟩ := bigOmega_eq_two_factors (by omega) hov
  have hSU : primeFactorSum u = a + b + c + d := by
    rw [heU, primeFactorSum_mul (mul_ne_zero (mul_ne_zero ha.ne_zero hb.ne_zero) hc.ne_zero) hd.ne_zero,
      primeFactorSum_mul (mul_ne_zero ha.ne_zero hb.ne_zero) hc.ne_zero,
      primeFactorSum_mul ha.ne_zero hb.ne_zero, primeFactorSum_prime ha,
      primeFactorSum_prime hb, primeFactorSum_prime hc, primeFactorSum_prime hd]
  have hSV : primeFactorSum v = r + s := by
    rw [heV, primeFactorSum_mul hr.ne_zero hs.ne_zero,
      primeFactorSum_prime hr, primeFactorSum_prime hs]
  have hpar := primeFactorSum_odd_parity huo
  have hro := hr.eq_two_or_odd
  have hso := hs.eq_two_or_odd
  have hcases : (r = 2 ∧ s = 2) ∨ (r % 2 = 1 ∧ s % 2 = 1) := by omega
  have hrs : r % 2 = 1 ∧ s % 2 = 1 := by
    rcases hcases with ⟨rfl, rfl⟩ | hh
    · have hv4 : v = 4 := by omega
      have huc : u = 15 ∨ u = 17 := by omega
      have h15 : bigOmega 15 = 2 := by
        change bigOmega (3 * 5) = 2
        rw [bigOmega_mul (by norm_num) (by norm_num), bigOmega_prime Nat.prime_three,
          bigOmega_prime (by norm_num : Nat.Prime 5)]
      rcases huc with rfl | rfl
      · norm_num [h15] at hou
      · norm_num [bigOmega_prime (by norm_num : Nat.Prime 17)] at hou
    · exact hh
  have h3 : 3 ∣ u ∨ 3 ∣ v := by
    by_contra! hn
    have hmu : u % 3 ≠ 0 := fun hh => hn.1 (Nat.dvd_iff_mod_eq_zero.mpr hh)
    have hmv : v % 3 ≠ 0 := fun hh => hn.2 (Nat.dvd_iff_mod_eq_zero.mpr hh)
    have hmp : p % 3 = 0 := by
      rcases hadj with hadd | hadd
      all_goals
        have heq := congrArg (fun z : ℕ => z % 3) hadd
        have hpq := congrArg (fun z : ℕ => z % 3) hcenter
        norm_num [Nat.add_mod, Nat.mul_mod] at heq hpq
        omega
    exact not_three_dvd_prime h.1 (by omega) (Nat.dvd_iff_mod_eq_zero.mpr hmp)
  have hnv : ¬ 3 ∣ v := by
    intro hv3
    have hmV := Nat.mod_eq_zero_of_dvd hv3
    have hnu : ¬ 3 ∣ u := by
      intro hu3
      have hmU := Nat.mod_eq_zero_of_dvd hu3
      omega
    have ha5 : 5 ≤ a := prime_five_le_of_dvd_odd ha
      (by refine ⟨b * c * d, ?_⟩; rw [heU]; ring) huo hnu
    have hb5 : 5 ≤ b := prime_five_le_of_dvd_odd hb
      (by refine ⟨a * c * d, ?_⟩; rw [heU]; ring) huo hnu
    have hc5 : 5 ≤ c := prime_five_le_of_dvd_odd hc
      (by refine ⟨a * b * d, ?_⟩; rw [heU]; ring) huo hnu
    have hd5 : 5 ≤ d := prime_five_le_of_dvd_odd hd
      (by refine ⟨a * b * c, ?_⟩; rw [heU]; ring) huo hnu
    have hbound := quadruple_factor_gap_bound ha5 hb5 hc5 hd5
    rw [← heU] at hbound
    have hdiv : 3 ∣ r * s := by simpa [heV] using hv3
    rcases Nat.prime_three.dvd_mul.mp hdiv with hrd | hsd
    · have hr3 : r = 3 := ((hr.eq_one_or_self_of_dvd 3 hrd).resolve_left (by norm_num)).symm
      subst r
      omega
    · have hs3 : s = 3 := ((hs.eq_one_or_self_of_dvd 3 hsd).resolve_left (by norm_num)).symm
      subst s
      omega
  have hdu : 3 ∣ u := h3.resolve_right hnv
  obtain ⟨w, hew⟩ := hdu
  have hw : w ≠ 0 := by intro hz; simp [hz] at hew; omega
  have how : bigOmega w = 3 := by
    rw [hew, bigOmega_mul (by norm_num) hw, bigOmega_prime Nat.prime_three] at hou
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := bigOmega_eq_three_factors hw how
  have hux : u = 3 * x * y * z := by rw [hew, hxyz]; ring
  have hx3 : 3 ≤ x := prime_three_le_of_dvd_odd hx
    (by refine ⟨3 * y * z, ?_⟩; rw [hux]; ring) huo
  have hy3 : 3 ≤ y := prime_three_le_of_dvd_odd hy
    (by refine ⟨3 * x * z, ?_⟩; rw [hux]; ring) huo
  have hz3 : 3 ≤ z := prime_three_le_of_dvd_odd hz
    (by refine ⟨3 * x * y, ?_⟩; rw [hux]; ring) huo
  have hxo := hx.mod_two_eq_one_iff_ne_two.mpr (by omega : x ≠ 2)
  have hyo := hy.mod_two_eq_one_iff_ne_two.mpr (by omega : y ≠ 2)
  have hzo := hz.mod_two_eq_one_iff_ne_two.mpr (by omega : z ≠ 2)
  have hfp : [3, x, y, z].prod = u := by simp [hux, mul_assoc]
  have hfprime : ∀ n ∈ [3, x, y, z], n.Prime := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;>
      first | exact hx | exact hy | exact hz | exact Nat.prime_three
  have hsumU := primeFactorSum_of_factors hfp hfprime
  norm_num at hsumU
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by have := h.1.two_le; omega)
  have h2u : 2 * u = 6 * x * y * z := by rw [hux]; ring
  have h8v : 8 * v = 8 * r * s := by rw [heV]; ring
  refine ⟨x, y, z, r, s, ?_, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hx, hxo⟩
    · exact ⟨hy, hyo⟩
    · exact ⟨hz, hzo⟩
    · exact ⟨hr, hrs.1⟩
    · exact ⟨hs, hrs.2⟩
  · rcases hadj with hadj | hadj
    · left
      constructor
      · rw [← h2u]; omega
      · rw [← h8v]; omega
    · right
      constructor
      · rw [← h2u]; omega
      · rw [← h8v]; omega
  · omega

theorem doubleBalanced_five_shape_iff {p : ℕ} (hp : p.Prime) :
    IsDoubleBalancedPrime p 5 ↔ HasDoubleFiveShape p :=
  ⟨doubleBalanced_five_has_shape, doubleBalanced_five_of_shape hp⟩

/-- The oriented level-five shape gives the signed gap `±1`. -/
theorem doubleBalanced_five_signed_gap {p : ℕ} (h : IsDoubleBalancedPrime p 5) :
    ∃ b c d r s : ℕ,
      (∀ z ∈ [b, c, d, r, s], z.Prime ∧ z % 2 = 1) ∧
      r + s + 1 = b + c + d ∧
      (4 * (r : ℤ) * s - 3 * (b : ℤ) * c * d = 1 ∨
       4 * (r : ℤ) * s - 3 * (b : ℤ) * c * d = -1) := by
  obtain ⟨b, c, d, r, s, hz, he, hsum⟩ := doubleBalanced_five_has_shape h
  refine ⟨b, c, d, r, s, hz, hsum, ?_⟩
  have hp2 := h.1.two_le
  rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · left
    have hnat : 8 * r * s = 6 * b * c * d + 2 := by omega
    have hint : (8 : ℤ) * r * s = 6 * b * c * d + 2 := by exact_mod_cast hnat
    nlinarith
  · right
    have hnat : 6 * b * c * d = 8 * r * s + 2 := by omega
    have hint : (6 : ℤ) * b * c * d = 8 * r * s + 2 := by exact_mod_cast hnat
    nlinarith

/-- Absolute-value form of the exact level-five neighbor gap. -/
theorem doubleBalanced_five_gap_natAbs {p : ℕ} (h : IsDoubleBalancedPrime p 5) :
    ∃ b c d r s : ℕ,
      (∀ z ∈ [b, c, d, r, s], z.Prime ∧ z % 2 = 1) ∧
      r + s + 1 = b + c + d ∧
      Int.natAbs (4 * (r : ℤ) * s - 3 * (b : ℤ) * c * d) = 1 := by
  obtain ⟨b, c, d, r, s, hz, hsum, hgap⟩ := doubleBalanced_five_signed_gap h
  refine ⟨b, c, d, r, s, hz, hsum, ?_⟩
  rcases hgap with hgap | hgap <;> rw [hgap] <;> norm_num

/-- A positive divisor-pair factorization recovers a level-five double-balanced prime.
The equations `x + K = 4r`, `y + K = 4s` are the division-free forms of
`r=(x+K)/4`, `s=(y+K)/4`; primality and the prime center remain explicit. -/
theorem doubleBalanced_five_of_factor_pair_pos {b c d r s : ℕ} {x y : ℤ}
    (hz : ∀ z ∈ [b, c, d, r, s], z.Prime ∧ z % 2 = 1)
    (hsum : r + s + 1 = b + c + d)
    (hx : x + 3 * (b : ℤ) * c = 4 * r)
    (hy : y + 3 * (b : ℤ) * c = 4 * s)
    (hxy : x * y =
      (3 * (b : ℤ) * c) * ((3 * (b : ℤ) * c) - 4 * ((b : ℤ) + c - 1)) +
        4 * (1 : ℤ))
    (hp : (6 * b * c * d + 1).Prime) :
    IsDoubleBalancedPrime (6 * b * c * d + 1) 5 := by
  have hsumZ : (r : ℤ) + s + 1 = b + c + d := by exact_mod_cast hsum
  have hdZ : (d : ℤ) = (r : ℤ) + s - ((b : ℤ) + c - 1) := by linarith
  have hgap := doubleFactorPair_recover
    (K := 3 * (b : ℤ) * c) (L := (b : ℤ) + c - 1)
    (r := (r : ℤ)) (s := (s : ℤ)) (d := (d : ℤ)) (e := 1)
    hx hy hxy hdZ
  have hgap2 : (8 : ℤ) * r * s = 6 * b * c * d + 2 := by nlinarith [hgap]
  have hnat : 8 * r * s = 6 * b * c * d + 2 := by exact_mod_cast hgap2
  apply doubleBalanced_five_of_shape hp
  refine ⟨b, c, d, r, s, hz, Or.inl ⟨?_, ?_⟩, hsum⟩ <;> omega

/-- The negative divisor-pair branch recovers the opposite orientation.
Negative integer factors `x,y` are permitted; only the recovered primes and center
are required positive through their primality hypotheses. -/
theorem doubleBalanced_five_of_factor_pair_neg {b c d r s : ℕ} {x y : ℤ}
    (hz : ∀ z ∈ [b, c, d, r, s], z.Prime ∧ z % 2 = 1)
    (hsum : r + s + 1 = b + c + d)
    (hx : x + 3 * (b : ℤ) * c = 4 * r)
    (hy : y + 3 * (b : ℤ) * c = 4 * s)
    (hxy : x * y =
      (3 * (b : ℤ) * c) * ((3 * (b : ℤ) * c) - 4 * ((b : ℤ) + c - 1)) +
        4 * (-1 : ℤ))
    (hp : (8 * r * s + 1).Prime) :
    IsDoubleBalancedPrime (8 * r * s + 1) 5 := by
  have hsumZ : (r : ℤ) + s + 1 = b + c + d := by exact_mod_cast hsum
  have hdZ : (d : ℤ) = (r : ℤ) + s - ((b : ℤ) + c - 1) := by linarith
  have hgap := doubleFactorPair_recover
    (K := 3 * (b : ℤ) * c) (L := (b : ℤ) + c - 1)
    (r := (r : ℤ)) (s := (s : ℤ)) (d := (d : ℤ)) (e := -1)
    hx hy hxy hdZ
  have hgap2 : (6 : ℤ) * b * c * d = 8 * r * s + 2 := by nlinarith [hgap]
  have hnat : 6 * b * c * d = 8 * r * s + 2 := by exact_mod_cast hgap2
  apply doubleBalanced_five_of_shape hp
  refine ⟨b, c, d, r, s, hz, Or.inr ⟨?_, ?_⟩, hsum⟩ <;> omega

theorem doubleBalanced_five_mod_forty_eight {p : ℕ}
    (h : IsDoubleBalancedPrime p 5) : p % 48 = 7 ∨ p % 48 = 41 :=
  doubleFiveShape_mod_forty_eight h.1.one_lt (doubleBalanced_five_has_shape h)

theorem doubleBalanced_five_not_twins {p : ℕ}
    (h : IsDoubleBalancedPrime p 5) (h' : IsDoubleBalancedPrime (p + 2) 5) : False :=
  doubleFiveShape_not_twins h.1.one_lt
    (doubleBalanced_five_has_shape h) (doubleBalanced_five_has_shape h')

/-- Double-balanced twin centers share a level, and it is at least six. -/
theorem doubleBalanced_twins_level_ge_six {p k j : ℕ}
    (h : IsDoubleBalancedPrime p k) (h' : IsDoubleBalancedPrime (p + 2) j) :
    6 ≤ k ∧ k = j := by
  have hk := doubleBalanced_level_ge_five h
  have he := doubleBalanced_twin_same_level h h'
  have hn : k ≠ 5 := by
    intro he5
    have hj : j = 5 := by omega
    subst k
    subst j
    exact doubleBalanced_five_not_twins h h'
  exact ⟨by omega, he⟩

end OmegaBalance
