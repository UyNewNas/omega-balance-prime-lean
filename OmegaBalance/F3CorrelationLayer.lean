import OmegaBalance.F3CorrelationFinite

/-!
# Signed layer kernel for the truncated F₃ correlation

This module combines the four residue-overlap counts for one pair of retained
3-adic layers.  The remaining complete-period correlation is a finite double
sum of this kernel.
-/

namespace OmegaBalance

/-- Signed contribution of layer `j` against layer `k` over one complete
`3^R` period.  The four terms correspond to positive/positive,
positive/negative, negative/positive and negative/negative residue targets. -/
def f3LayerCorrelation (R j k h : ℕ) : ℤ :=
  (modShiftPairCount R j k (3 ^ j - 1) (3 ^ k - 1) h : ℤ) -
  (modShiftPairCount R j k (3 ^ j - 1) 1 h : ℤ) -
  (modShiftPairCount R j k 1 (3 ^ k - 1) h : ℤ) +
  (modShiftPairCount R j k 1 1 h : ℤ)

/-- Exact signed one-layer-pair kernel.  Same-sign overlaps contribute twice
at `h ≡ 0`; the two cross-sign overlaps subtract the `h ≡ 2` and `h+2 ≡ 0`
classes.  No infinite limit is used here. -/
theorem f3LayerCorrelation_eq {R j k h : ℕ} (hjR : j ≤ R) (hkR : k ≤ R) :
    f3LayerCorrelation R j k h =
      (if h ≡ 0 [MOD 3 ^ min j k] then 2 * (3 ^ (R - max j k) : ℤ) else 0) -
      (if h ≡ 2 [MOD 3 ^ min j k] then (3 ^ (R - max j k) : ℤ) else 0) -
      (if h + 2 ≡ 0 [MOD 3 ^ min j k] then (3 ^ (R - max j k) : ℤ) else 0) := by
  unfold f3LayerCorrelation
  rw [modShiftPairCount_pos_pos_eq hjR hkR,
    modShiftPairCount_pos_neg_eq hjR hkR,
    modShiftPairCount_neg_pos_eq hjR hkR,
    modShiftPairCount_neg_neg_eq hjR hkR]
  split_ifs <;> ring

end OmegaBalance
