import OmegaBalance.F3Finite
import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite residue-overlap counts for the F₃ correlation calculation

This module proves the exact finite counting lemma needed before expanding the
truncated correlation.  It does not assert any infinite Cesàro limit.
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

/-- Ordered version of the nested-modulus overlap count.  If `j ≤ k`, the two
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

/-- Symmetric overlap count.  Compatibility is tested modulo the smaller
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

end OmegaBalance
