import OmegaBalance.F3SignChanges

namespace OmegaBalance

def f3RunModulus (c : ℤ) : ℕ :=
  3 ^ (c.natAbs + 1)

def f3RunResidue (c : ℤ) : ℕ :=
  if 0 < c then 3 ^ c.natAbs - 1 else 3 ^ c.natAbs + 1

theorem f3RunModulus_ge_three (c : ℤ) :
    3 ≤ f3RunModulus c := by
  rw [f3RunModulus, pow_succ]
  have hp : 0 < (3 : ℕ) ^ c.natAbs := pow_pos (by decide) _
  omega

theorem f3RunResidue_lt_modulus {c : ℤ} (hc : c ≠ 0) :
    f3RunResidue c < f3RunModulus c := by
  by_cases hpos : 0 < c
  · simp only [f3RunResidue, hpos, if_true, f3RunModulus, pow_succ]
    have hp : 0 < (3 : ℕ) ^ c.natAbs := pow_pos (by decide) _
    omega
  · simp only [f3RunResidue, hpos, if_false, f3RunModulus, pow_succ]
    have hp : 0 < (3 : ℕ) ^ c.natAbs := pow_pos (by decide) _
    omega

theorem f3RunResidue_coprime {c : ℤ} (hc : c ≠ 0) :
    (f3RunResidue c).Coprime (f3RunModulus c) := by
  have hk : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  by_cases hpos : 0 < c
  · simpa [f3RunResidue, f3RunModulus, hpos] using
      (f3_pos_residue_coprime (k := c.natAbs) hk)
  · simpa [f3RunResidue, f3RunModulus, hpos] using
      (f3_neg_residue_coprime (k := c.natAbs) hk)

theorem f3_of_modEq_runResidue {n : ℕ} {c : ℤ}
    (hn : 1 < n) (hc : c ≠ 0)
    (hmod : n ≡ f3RunResidue c [MOD f3RunModulus c]) :
    f3 n = c := by
  have hk : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  by_cases hpos : 0 < c
  · have hm : n ≡ 3 ^ c.natAbs - 1 [MOD 3 ^ (c.natAbs + 1)] := by
      simpa [f3RunResidue, f3RunModulus, hpos] using hmod
    have hf := f3_pos_of_modEq_level hn hk hm
    have he : (c.natAbs : ℤ) = c := by
      rw [Int.natCast_natAbs, abs_of_pos hpos]
    simpa [he] using hf
  · have hneg : c < 0 := by omega
    have hm : n ≡ 3 ^ c.natAbs + 1 [MOD 3 ^ (c.natAbs + 1)] := by
      simpa [f3RunResidue, f3RunModulus, hpos] using hmod
    have hf := f3_neg_of_modEq_level hn hk hm
    have he : -(c.natAbs : ℤ) = c := by
      rw [Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
    simpa [he] using hf

end OmegaBalance
