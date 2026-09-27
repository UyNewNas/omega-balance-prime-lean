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


theorem bftb_exists_crt_shift
    {T H : Finset ℕ} {g : ℕ} (q : ℕ → ℕ)
    (hqprime : ∀ t ∈ T, (q t).Prime)
    (hpair : Set.Pairwise (↑T : Set ℕ)
      (fun s t => (q s).Coprime (q t)))
    (hgq : ∀ t ∈ T, g.Coprime (q t))
    (hsafe : ∀ t ∈ T, ∀ h ∈ H, ¬ (h ≡ t [MOD q t])) :
    ∃ A : ℕ,
      (∀ t ∈ T, q t ∣ g * A + t) ∧
      (∀ t ∈ T, ∀ h ∈ H, ¬ q t ∣ g * A + h) := by
  classical
  choose! r hr using fun t (ht : t ∈ T) =>
    bftb_exists_crt_residue g (q t) t (hgq t ht) (hqprime t ht).ne_zero
  let cr := Nat.chineseRemainderOfFinset r q T
    (fun t ht => (hqprime t ht).ne_zero) hpair
  refine ⟨(cr : ℕ), ?_, ?_⟩
  · intro t ht
    have hcrt : (cr : ℕ) ≡ r t [MOD q t] := cr.property t ht
    have htransport : g * (cr : ℕ) + t ≡ g * r t + t [MOD q t] :=
      (hcrt.mul_left g).add_right t
    exact Nat.modEq_zero_iff_dvd.mp (htransport.trans (hr t ht))
  · intro t ht h hh hdiv
    have hcrt : (cr : ℕ) ≡ r t [MOD q t] := cr.property t ht
    have htzero : g * (cr : ℕ) + t ≡ 0 [MOD q t] :=
      ((hcrt.mul_left g).add_right t).trans (hr t ht)
    have hhzero : g * (cr : ℕ) + h ≡ 0 [MOD q t] :=
      Nat.modEq_zero_iff_dvd.mpr hdiv
    have hht : h ≡ t [MOD q t] :=
      Nat.ModEq.add_left_cancel' (g * (cr : ℕ)) (hhzero.trans htzero.symm)
    exact hsafe t ht h hh hht

end OmegaBalance
