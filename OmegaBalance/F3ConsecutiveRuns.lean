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


/-- A finite block of genuinely consecutive primes in the full prime sequence. -/
def ConsecutivePrimeBlock : List ℕ → Prop
  | [] => True
  | p :: [] => p.Prime
  | p :: q :: ps => ConsecutivePrimes p q ∧ ConsecutivePrimeBlock (q :: ps)

/-- A genuine consecutive-prime block in one residue class, beyond a lower bound. -/
def ConsecutivePrimeRunInClass (a D L B : ℕ) : Prop :=
  ∃ ps : List ℕ,
    ps.length = L ∧
    ConsecutivePrimeBlock ps ∧
    (∀ p ∈ ps, B < p) ∧
    (∀ p ∈ ps, p ≡ a [MOD D])

/-- A genuine consecutive-prime block of length L on which F₃ is constantly c. -/
def F3ConsecutiveRun (c : ℤ) (L B : ℕ) : Prop :=
  ∃ ps : List ℕ,
    ps.length = L ∧
    ConsecutivePrimeBlock ps ∧
    (∀ p ∈ ps, B < p) ∧
    (∀ p ∈ ps, f3 p = c)

/-- Residue-class consecutive blocks transfer to exact constant-F₃ blocks. -/
theorem f3ConsecutiveRun_of_residueRun {c : ℤ} (hc : c ≠ 0) {L B : ℕ}
    (h : ConsecutivePrimeRunInClass
      (f3RunResidue c) (f3RunModulus c) L (max B 1)) :
    F3ConsecutiveRun c L B := by
  rcases h with ⟨ps, hlen, hblock, hB, hmod⟩
  refine ⟨ps, hlen, hblock, ?_, ?_⟩
  · intro p hp
    exact lt_of_le_of_lt (Nat.le_max_left B 1) (hB p hp)
  · intro p hp
    have hp1 : 1 < p :=
      lt_of_le_of_lt (Nat.le_max_right B 1) (hB p hp)
    exact f3_of_modEq_runResidue hp1 hc (hmod p hp)

/-- Arbitrarily far residue-class blocks imply arbitrarily far exact F₃ blocks. -/
theorem f3ConsecutiveRuns_of_residueRuns {c : ℤ} (hc : c ≠ 0) {L : ℕ}
    (h : ∀ B : ℕ, ConsecutivePrimeRunInClass
      (f3RunResidue c) (f3RunModulus c) L B) :
    ∀ B : ℕ, F3ConsecutiveRun c L B := by
  intro B
  exact f3ConsecutiveRun_of_residueRun hc (h (max B 1))

end OmegaBalance
