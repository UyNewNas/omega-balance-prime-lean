import OmegaBalance.F3ConsecutivePrimeIndex

namespace OmegaBalance

/--
Local compatibility predicate matching the mathematical shape of
`Finset.Admissible` in AxiomMath/PrimeGapsLib
(commit `1faa7b14e82ddebc2772dfb9153922f01b106477`,
`PrimeGapsTheory/NumberTheory/Admissible.lean`).

We keep it local instead of adding the upstream repository as a dependency:
for every prime modulus, the finite set misses at least one residue class.
-/
def BFTBAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ h ∈ H, ¬ (h ≡ r [MOD p])

/-- The affine tuple used in BFTB Corollary 3: h ↦ D*h+a. -/
def bftbAffineOffsets (a D : ℕ) (H : Finset ℕ) : Finset ℕ :=
  H.image (fun h => D * h + a)

/--
Admissibility is preserved by the BFTB affine change of variables.

No coprimality hypothesis on `a,D` is needed for this statement:
if `p ∣ D`, the affine tuple occupies one residue class modulo `p`;
if `p ∤ D`, multiplication by `D` can be cancelled modulo the prime `p`.
The separate reduced-class condition `a.Coprime D` is handled by
`bftbAffineResidue_coprime`.
-/
theorem bftbAffineOffsets_admissible
    {H : Finset ℕ} (hH : BFTBAdmissible H) (a D : ℕ) :
    BFTBAdmissible (bftbAffineOffsets a D H) := by
  intro p hp
  by_cases hpD : p ∣ D
  · refine ⟨a + 1, ?_⟩
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    intro hbad
    have hDt : D * t ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpD t)
    have haff : D * t + a ≡ a [MOD p] := by\n      simpa using hDt.add_right a
    have hstep : a ≡ a + 1 [MOD p] := haff.symm.trans hbad
    have hpone : p ∣ 1 := by
      simpa using (Nat.modEq_iff_dvd' (Nat.le_succ a)).mp hstep
    exact hp.not_dvd_one hpone
  · rcases hH p hp with ⟨r, hr⟩
    refine ⟨D * r + a, ?_⟩
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    intro hbad
    have hmul : D * t ≡ D * r [MOD p] :=
      Nat.ModEq.add_right_cancel' a hbad
    have hcop : p.Coprime D :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 hpD
    have htr : t ≡ r [MOD p] :=
      Nat.ModEq.cancel_left_of_coprime hcop hmul
    exact hr t ht htr

/--
For a reduced class `a mod D`, every affine offset `D*h+a` is itself
coprime to `D`. This packages the pointwise arithmetic lemma at tuple level.
-/
theorem bftbAffineOffsets_all_coprime
    {H : Finset ℕ} {a D : ℕ} (ha : a.Coprime D) :
    ∀ b ∈ bftbAffineOffsets a D H, b.Coprime D := by
  intro b hb
  rcases Finset.mem_image.mp hb with ⟨t, ht, rfl⟩
  exact bftbAffineResidue_coprime ha t

end OmegaBalance
