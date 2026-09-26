import OmegaBalance.F3PrimeDensityAPLimit

namespace OmegaBalance

/-- For a positive power of three, residue one is the same as divisibility of
the predecessor.  This is the small congruence bridge needed to turn the
valuation description of exact negative F₃ levels into AP predicates. -/
lemma f3_mod_pow_three_eq_one_iff_dvd_sub_one
    {p k : ℕ} (hp : 1 ≤ p) (hk : 0 < k) :
    p % (3 ^ k) = 1 ↔ 3 ^ k ∣ p - 1 := by
  have hm : 1 < 3 ^ k :=
    Nat.one_lt_pow hk.ne' (by norm_num : 1 < (3 : ℕ))
  have h := Nat.modEq_iff_dvd'
    (n := 3 ^ k) (a := 1) (b := p) hp
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hm, eq_comm] using h

/-- On primes above three, an exact negative F₃ level is exactly the residue-one
class modulo `3^k` with the residue-one class modulo `3^(k+1)` removed. -/
theorem f3_prime_eq_neg_level_iff_nested_residue
    {p k : ℕ} (hp : p.Prime) (h3 : 3 < p) (hk : 0 < k) :
    f3 p = -(k : ℤ) ↔
      p % (3 ^ k) = 1 ∧ p % (3 ^ (k + 1)) ≠ 1 := by
  rw [f3_prime_eq_neg_level_iff hp h3 hk]
  constructor
  · rintro ⟨hkdiv, hksdiv⟩
    constructor
    · exact (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le hk).2 hkdiv
    · intro hmod
      exact hksdiv <|
        (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le (by omega)).1 hmod
  · rintro ⟨hkmod, hksmod⟩
    constructor
    · exact (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le hk).1 hkmod
    · intro hdiv
      exact hksmod <|
        (f3_mod_pow_three_eq_one_iff_dvd_sub_one hp.one_lt.le (by omega)).2 hdiv

end OmegaBalance
