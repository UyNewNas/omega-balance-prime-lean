import OmegaBalance.F3SumProduct
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Infinitely many primes at each exact F₃ level

Reuse the pinned mathlib proof of Dirichlet's theorem. The natural-number
wrapper below depends on `Nat.infinite_setOfPred_prime_and_eq_mod`; there is
no new number-theoretic assumption. One reduced residue class per sign is
enough for infinitude, but is NOT an enumeration of the entire level set.
No density, consecutive-prime, bounded-gap or twin-infinitude assertion is
hidden in the statements of this module.
-/

namespace OmegaBalance

/-- The positive-level residue is reduced modulo every power of three. -/
theorem f3_pos_residue_coprime {k : ℕ} (hk : 0 < k) :
    (3 ^ k - 1).Coprime (3 ^ (k + 1)) := by
  have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
  have hd : 3 ∣ (3 : ℕ) ^ k := dvd_pow_self 3 (by omega)
  have hc : (3 ^ k - 1).Coprime 3 := by
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hm' := Nat.mod_eq_zero_of_dvd h
    omega
  exact hc.pow_right (k + 1)

/-- The negative-level residue is also reduced. -/
theorem f3_neg_residue_coprime {k : ℕ} (hk : 0 < k) :
    (3 ^ k + 1).Coprime (3 ^ (k + 1)) := by
  have hd : 3 ∣ (3 : ℕ) ^ k := dvd_pow_self 3 (by omega)
  have hc : (3 ^ k + 1).Coprime 3 := by
    apply Nat.Coprime.symm
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro h
    have hm := Nat.mod_eq_zero_of_dvd hd
    have hm' := Nat.mod_eq_zero_of_dvd h
    omega
  exact hc.pow_right (k + 1)

/-- A single explicit residue class gives the exact value +k, not just depth ≥ k. -/
theorem f3_pos_of_modEq_level {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hmod : n ≡ 3 ^ k - 1 [MOD 3 ^ (k + 1)]) :
    f3 n = (k : ℤ) := by
  have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
  have hsmall : 3 ^ k - 1 < (3 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    omega
  have hr : n % 3 ^ (k + 1) = 3 ^ k - 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hsmall] using hmod
  have he := Nat.mod_add_div n (3 ^ (k + 1))
  rw [hr, pow_succ] at he
  have hsub : 3 ^ k - 1 + 1 = (3 : ℕ) ^ k := by omega
  have hf : n + 1 = 3 ^ k * (1 + 3 * (n / 3 ^ (k + 1))) := by
    nlinarith [he, hsub]
  have hv0 : v3 (1 + 3 * (n / 3 ^ (k + 1))) = 0 := by
    apply v3_eq_zero_of_not_dvd
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  have hv : v3 (n + 1) = k := by
    rw [hf, v3_mul (by positivity) (by omega), v3_pow_three, hv0, add_zero]
  have hd : 3 ∣ n + 1 :=
    (dvd_pow_self 3 (by omega : k ≠ 0)).trans ⟨_, hf⟩
  have hm : n % 3 = 2 := by
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [(f3_of_mod_three_two hn hm).1, hv]

/-- A single explicit residue class gives the exact value -k. -/
theorem f3_neg_of_modEq_level {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (hmod : n ≡ 3 ^ k + 1 [MOD 3 ^ (k + 1)]) :
    f3 n = -(k : ℤ) := by
  have hp : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
  have hsmall : 3 ^ k + 1 < (3 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    omega
  have hr : n % 3 ^ (k + 1) = 3 ^ k + 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hsmall] using hmod
  have he := Nat.mod_add_div n (3 ^ (k + 1))
  rw [hr, pow_succ] at he
  have hsub : n - 1 + 1 = n := by omega
  have hf : n - 1 = 3 ^ k * (1 + 3 * (n / 3 ^ (k + 1))) := by
    nlinarith [he, hsub]
  have hv0 : v3 (1 + 3 * (n / 3 ^ (k + 1))) = 0 := by
    apply v3_eq_zero_of_not_dvd
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  have hv : v3 (n - 1) = k := by
    rw [hf, v3_mul (by positivity) (by omega), v3_pow_three, hv0, add_zero]
  have hd : 3 ∣ n - 1 :=
    (dvd_pow_self 3 (by omega : k ≠ 0)).trans ⟨_, hf⟩
  have hm : n % 3 = 1 := by
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  rw [(f3_of_mod_three_one hn hm).1, hv]

/-- An arbitrarily large prime with exact positive level. -/
theorem exists_prime_gt_f3_pos {k : ℕ} (hk : 0 < k) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ 3 < p ∧ p.Prime ∧ f3 p = (k : ℤ) := by
  obtain ⟨p, hB, hp, hm⟩ := Nat.forall_exists_prime_gt_and_modEq (max B 3)
    (pow_ne_zero (k + 1) (by decide : (3 : ℕ) ≠ 0)) (f3_pos_residue_coprime hk)
  have hpB : B < p := lt_of_le_of_lt (le_max_left B 3) hB
  have hp3 : 3 < p := lt_of_le_of_lt (le_max_right B 3) hB
  exact ⟨p, hpB, hp3, hp, f3_pos_of_modEq_level (by omega) hk hm⟩

/-- An arbitrarily large prime with exact negative level. -/
theorem exists_prime_gt_f3_neg {k : ℕ} (hk : 0 < k) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ 3 < p ∧ p.Prime ∧ f3 p = -(k : ℤ) := by
  obtain ⟨p, hB, hp, hm⟩ := Nat.forall_exists_prime_gt_and_modEq (max B 3)
    (pow_ne_zero (k + 1) (by decide : (3 : ℕ) ≠ 0)) (f3_neg_residue_coprime hk)
  have hpB : B < p := lt_of_le_of_lt (le_max_left B 3) hB
  have hp3 : 3 < p := lt_of_le_of_lt (le_max_right B 3) hB
  exact ⟨p, hpB, hp3, hp, f3_neg_of_modEq_level (by omega) hk hm⟩

theorem f3_prime_level_pos_infinite {k : ℕ} (hk : 0 < k) :
    {p : ℕ | p.Prime ∧ 3 < p ∧ f3 p = (k : ℤ)}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨p, hB, h3, hp, hf⟩ := exists_prime_gt_f3_pos hk B
  exact ⟨p, ⟨hp, h3, hf⟩, hB⟩

theorem f3_prime_level_neg_infinite {k : ℕ} (hk : 0 < k) :
    {p : ℕ | p.Prime ∧ 3 < p ∧ f3 p = -(k : ℤ)}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨p, hB, h3, hp, hf⟩ := exists_prime_gt_f3_neg hk B
  exact ⟨p, ⟨hp, h3, hf⟩, hB⟩

/-- Every nonzero signed integer is attained by infinitely many primes > 3. -/
theorem f3_prime_level_infinite {c : ℤ} (hc : c ≠ 0) :
    {p : ℕ | p.Prime ∧ 3 < p ∧ f3 p = c}.Infinite := by
  have hk : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  by_cases hpos : 0 < c
  · have he : (c.natAbs : ℤ) = c := by
      rw [Int.natCast_natAbs, abs_of_pos hpos]
    simpa only [he] using f3_prime_level_pos_infinite hk
  · have hneg : c < 0 := by omega
    have he : -(c.natAbs : ℤ) = c := by
      rw [Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
    simpa only [he] using f3_prime_level_neg_infinite hk

/-- The excluded value zero has no prime witness above three. -/
theorem f3_prime_zero_level_empty :
    {p : ℕ | p.Prime ∧ 3 < p ∧ f3 p = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hp, h3, hf⟩
  exact f3_ne_zero_of_prime hp h3 hf

/-- Existence of opposite exact levels, without any claim about the gap. -/
theorem exists_ordered_prime_opposite_levels {k : ℕ} (hk : 0 < k) (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ 3 < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
      f3 p = (k : ℤ) ∧ f3 q = -(k : ℤ) := by
  obtain ⟨p, hB, hp3, hp, hfp⟩ := exists_prime_gt_f3_pos hk B
  obtain ⟨q, hpq, _, hq, hfq⟩ := exists_prime_gt_f3_neg hk p
  exact ⟨p, q, hB, hp3, hpq, hp, hq, hfp, hfq⟩

end OmegaBalance
