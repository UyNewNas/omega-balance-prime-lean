import OmegaBalance.F3Finite
import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite residue-overlap counts for the F₃ correlation calculation

This module proves the exact finite counting lemmas needed before expanding the
truncated correlation. It does not assert any infinite Cesàro limit.
-/

namespace OmegaBalance

/-- Number of residues in a complete `3^R` period satisfying two power-of-three
congruence conditions. -/
def modPairCount (R j k a b : ℕ) : ℕ :=
  ((Finset.range (3 ^ R)).filter fun n =>
    n ≡ a [MOD 3 ^ j] ∧ n ≡ b [MOD 3 ^ k]).card

/-- A single residue class modulo `3^k` occurs exactly `3^(R-k)` times in a
complete `3^R` period, provided `k ≤ R`. -/
theorem card_filter_range_modEq_pow_three {R k b : ℕ} (hkR : k ≤ R) :
    ((Finset.range (3 ^ R)).filter fun n => n ≡ b [MOD 3 ^ k]).card =
      3 ^ (R - k) := by
  rw [← Nat.count_eq_card_filter_range]
  rw [Nat.count_modEq_card (b := 3 ^ R) (r := 3 ^ k) (by positivity) b]
  have hdiv : 3 ^ k ∣ 3 ^ R := pow_dvd_pow 3 hkR
  rw [Nat.mod_eq_zero_of_dvd hdiv]
  simp only [Nat.not_lt_zero, if_false, add_zero]
  exact Nat.pow_div hkR (by decide)

/-- Ordered version of the nested-modulus overlap count. If `j ≤ k`, the two
conditions are compatible exactly when their target residues agree modulo
`3^j`; in the compatible case the stronger class modulo `3^k` determines the
intersection. -/
theorem modPairCount_eq_of_le {R j k a b : ℕ} (hjk : j ≤ k) (hkR : k ≤ R) :
    modPairCount R j k a b =
      if a ≡ b [MOD 3 ^ j] then 3 ^ (R - k) else 0 := by
  unfold modPairCount
  have hjk_dvd : 3 ^ j ∣ 3 ^ k := pow_dvd_pow 3 hjk
  by_cases hab : a ≡ b [MOD 3 ^ j]
  · rw [if_pos hab]
    have hfilter :
        (Finset.range (3 ^ R)).filter (fun n =>
            n ≡ a [MOD 3 ^ j] ∧ n ≡ b [MOD 3 ^ k]) =
          (Finset.range (3 ^ R)).filter (fun n => n ≡ b [MOD 3 ^ k]) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hnR, _, hnk⟩
        exact ⟨hnR, hnk⟩
      · rintro ⟨hnR, hnk⟩
        have hnj_b : n ≡ b [MOD 3 ^ j] := hnk.of_dvd hjk_dvd
        have hnj_a : n ≡ a [MOD 3 ^ j] := hnj_b.trans hab.symm
        exact ⟨hnR, hnj_a, hnk⟩
    rw [hfilter, card_filter_range_modEq_pow_three hkR]
  · rw [if_neg hab]
    have hfilter :
        (Finset.range (3 ^ R)).filter (fun n =>
            n ≡ a [MOD 3 ^ j] ∧ n ≡ b [MOD 3 ^ k]) = ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
      rintro ⟨_, hnj, hnk⟩
      apply hab
      exact hnj.symm.trans (hnk.of_dvd hjk_dvd)
    rw [hfilter, Finset.card_empty]

/-- Symmetric overlap count. Compatibility is tested modulo the smaller
power, while a compatible intersection has the size of one class modulo the
larger power. -/
theorem modPairCount_eq {R j k a b : ℕ} (hjR : j ≤ R) (hkR : k ≤ R) :
    modPairCount R j k a b =
      if a ≡ b [MOD 3 ^ min j k] then 3 ^ (R - max j k) else 0 := by
  by_cases hjk : j ≤ k
  · rw [modPairCount_eq_of_le hjk hkR]
    simp only [min_eq_left hjk, max_eq_right hjk]
  · have hkj : k ≤ j := Nat.le_of_lt (Nat.lt_of_not_ge hjk)
    have hswap : modPairCount R j k a b = modPairCount R k j b a := by
      unfold modPairCount
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    rw [hswap, modPairCount_eq_of_le hkj hjR]
    simp only [min_eq_right hkj, max_eq_left hkj]
    by_cases hab : a ≡ b [MOD 3 ^ k]
    · have hba : b ≡ a [MOD 3 ^ k] := hab.symm
      simp [hab, hba]
    · have hba : ¬ b ≡ a [MOD 3 ^ k] := fun h => hab h.symm
      simp [hab, hba]

/-- A natural-number representative of the residue `b - h (mod q)` chosen
large enough that subtraction is not truncated. -/
def shiftResidue (q h b : ℕ) : ℕ := b + q * (h + 1) - h

/-- The chosen shifted representative satisfies an exact equality before
passing to congruences. -/
theorem shiftResidue_add {q h b : ℕ} (hq : 0 < q) :
    shiftResidue q h b + h = b + q * (h + 1) := by
  unfold shiftResidue
  have hq1 : 1 ≤ q := hq
  have hmul : h + 1 ≤ q * (h + 1) := by
    simpa using Nat.mul_le_mul_right (h + 1) hq1
  have hh : h ≤ b + q * (h + 1) := by omega
  exact Nat.sub_add_cancel hh

/-- Adding the shift back sends `shiftResidue q h b` to `b` modulo `q`. -/
theorem shiftResidue_add_modEq {q h b : ℕ} (hq : 0 < q) :
    shiftResidue q h b + h ≡ b [MOD q] := by
  rw [shiftResidue_add hq]
  simpa [Nat.add_comm] using
    (Nat.ModEq.modulus_mul_add (m := q) (a := h + 1) (b := b))

/-- Congruence against the shifted representative is equivalent to shifting
the variable itself. The statement is deliberately relative to any divisor
`m ∣ q`, which is what the smaller modulus in `modPairCount_eq` needs. -/
theorem modEq_shiftResidue_iff_of_dvd {m q h a b : ℕ} (hmq : m ∣ q) (hq : 0 < q) :
    a ≡ shiftResidue q h b [MOD m] ↔ a + h ≡ b [MOD m] := by
  have hs : shiftResidue q h b + h ≡ b [MOD m] :=
    (shiftResidue_add_modEq (q := q) (h := h) (b := b) hq).of_dvd hmq
  constructor
  · intro ha
    exact (ha.add_right h).trans hs
  · intro hab
    have hboth : a + h ≡ shiftResidue q h b + h [MOD m] := hab.trans hs.symm
    exact hboth.add_right_cancel' h

/-- Number of residues in a complete `3^R` period satisfying one ordinary
power-of-three congruence and one congruence after translation by `h`. -/
def modShiftPairCount (R j k a b h : ℕ) : ℕ :=
  ((Finset.range (3 ^ R)).filter fun n =>
    n ≡ a [MOD 3 ^ j] ∧ n + h ≡ b [MOD 3 ^ k]).card

/-- A translated congruence can be represented by an ordinary target residue,
without changing the complete-period count. -/
theorem modShiftPairCount_eq_modPairCount {R j k a b h : ℕ} :
    modShiftPairCount R j k a b h =
      modPairCount R j k a (shiftResidue (3 ^ k) h b) := by
  unfold modShiftPairCount modPairCount
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  have hiff :
      n ≡ shiftResidue (3 ^ k) h b [MOD 3 ^ k] ↔
        n + h ≡ b [MOD 3 ^ k] :=
    modEq_shiftResidue_iff_of_dvd (m := 3 ^ k) (q := 3 ^ k) (h := h)
      (a := n) (b := b) dvd_rfl (pow_pos (by decide) k)
  tauto

/-- Exact complete-period overlap count with a translation. Compatibility is
now expressed directly as `a + h ≡ b` modulo the smaller power. This is the
form needed by the four sign terms in the truncated F₃ correlation. -/
theorem modShiftPairCount_eq {R j k a b h : ℕ} (hjR : j ≤ R) (hkR : k ≤ R) :
    modShiftPairCount R j k a b h =
      if a + h ≡ b [MOD 3 ^ min j k] then 3 ^ (R - max j k) else 0 := by
  rw [modShiftPairCount_eq_modPairCount, modPairCount_eq hjR hkR]
  have hdiv : 3 ^ min j k ∣ 3 ^ k := pow_dvd_pow 3 (min_le_right j k)
  have hcompat :
      a ≡ shiftResidue (3 ^ k) h b [MOD 3 ^ min j k] ↔
        a + h ≡ b [MOD 3 ^ min j k] :=
    modEq_shiftResidue_iff_of_dvd hdiv (pow_pos (by decide) k)
  by_cases hab : a + h ≡ b [MOD 3 ^ min j k]
  · rw [if_pos hab, if_pos (hcompat.mpr hab)]
  · rw [if_neg hab, if_neg]
    intro ha
    exact hab (hcompat.mp ha)

end OmegaBalance
