import OmegaBalance.F3BFTBAdmissible
import Mathlib.Data.Nat.ChineseRemainder

namespace OmegaBalance

/-- Solve one linear congruence used by the finite BFTB CRT construction. -/
theorem bftb_exists_crt_residue (g q t : ℕ)
    (hgq : g.Coprime q) (hq : q ≠ 0) :
    ∃ r : ℕ, g * r + t ≡ 0 [MOD q] := by
  obtain ⟨r, hrlt, hr⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (q - t % q) hgq hq
  refine ⟨r, ?_⟩
  have hmul : g * r ≡ q - t % q [MOD q] := by
    simpa [Nat.ModEq] using hr
  have htmod : t ≡ t % q [MOD q] := (Nat.mod_modEq t q).symm
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  have hle : t % q ≤ q := (Nat.mod_lt t hqpos).le
  have hsum : g * r + t ≡ q [MOD q] := by
    have h := hmul.add htmod
    simpa [Nat.sub_add_cancel hle] using h
  exact hsum.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl q))

end OmegaBalance
